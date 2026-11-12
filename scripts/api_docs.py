#!/usr/bin/env python3
"""Helpers for scripts/build_api_docs.sh, which builds the API documentation of SHSLib.

doc-gen4 documents a library's whole import closure, Mathlib included. The build script runs it
only on the modules this site publishes. This script supplies the steps around that run:

  modules        Print `<module> <source URI>` for each published module: the SHSLib library, and
                 the modules it imports from packages that the Mathlib documentation does not cover
                 (BrownianMotion and KolmogorovExtension4). The source URI is the one doc-gen4's
                 `srcUri.github` Lake facet computes.

  link DOC_DIR   Point every link that leaves the published pages at the Mathlib documentation,
                 https://leanprover-community.github.io/mathlib4_docs/, which covers Mathlib, its
                 dependencies (Batteries, Aesop, ...) and Lean core. A link goes to the current page
                 of its declaration or module there. A name that no longer exists there goes to its
                 source file on GitHub at the version SHSLib pins. If that site's index can't be
                 downloaded (or with --offline), declaration links go through its `find` page.
                 Fails on a link to a published page that doesn't exist.

  check DOC_DIR  Fail unless every published module has a page and every entry of references.bib is
                 on references.html. (doc-gen4 drops the citations silently when the bibliography
                 step went wrong.)

Usage: scripts/api_docs.py modules | link DOC_DIR [--offline] | check DOC_DIR
"""

import collections
import html
import json
import os
import pathlib
import posixpath
import re
import subprocess
import sys
import urllib.parse
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
PACKAGES = ROOT / ".lake" / "packages"
LIBRARY = "SHSLib"
MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/"
LEAN_CORE = ("Init", "Std", "Lean", "Lake")
IMPORT = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)")
SCHEME = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")
HREF = re.compile(r'href="([^"]*)"')


def header_imports(path):
    """The modules that the Lean file `path` imports."""
    imports, depth = [], 0
    for line in path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if depth:
            depth += s.count("/-") - s.count("-/")
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith(("/-!", "/--")):
            break  # a docstring is a command: the header is over
        if s.startswith("/-"):
            depth = s.count("/-") - s.count("-/")
            continue
        s = s.split("--", 1)[0].strip()
        if s in ("module", "prelude"):
            continue
        m = IMPORT.match(s)
        if not m:
            break
        imports.append(m.group(1))
    return imports


def module_name(path, base):
    return ".".join(path.relative_to(base).with_suffix("").parts)


def library_modules():
    """The modules of the SHSLib library (lakefile glob `SHSLib.*`): name -> file."""
    mods = {LIBRARY: ROOT / f"{LIBRARY}.lean"}
    for p in sorted((ROOT / LIBRARY).rglob("*.lean")):
        mods[module_name(p, ROOT)] = p
    return mods


def package_modules():
    """The modules of the packages in .lake/packages: name -> (package directory, file)."""
    mods = {}
    for pkg in sorted(PACKAGES.iterdir()):
        if not pkg.is_dir():
            continue
        for dirpath, dirnames, files in os.walk(pkg):
            dirnames[:] = [d for d in dirnames if not d.startswith(".")]
            for f in files:
                if f.endswith(".lean"):
                    p = pathlib.Path(dirpath, f)
                    mods.setdefault(module_name(p, pkg), (pkg, p))
    return mods


def mathlib_docs_packages():
    """Packages that the Mathlib documentation covers: Mathlib and its dependencies."""
    manifest = json.loads((PACKAGES / "mathlib" / "lake-manifest.json").read_text())
    return {"mathlib"} | {p["name"] for p in manifest["packages"]}


def published_modules():
    """The modules this site documents: module name -> (git checkout, file)."""
    lib, pkgs, covered = library_modules(), package_modules(), mathlib_docs_packages()
    published, seen, todo = {}, set(), list(lib)
    while todo:
        m = todo.pop()
        if m in seen or m.split(".")[0] in LEAN_CORE:
            continue
        seen.add(m)
        if m in lib:
            published[m], path = (ROOT, lib[m]), lib[m]
        elif m in pkgs:
            pkg, path = pkgs[m]
            if pkg.name in covered:
                continue  # documented on the Mathlib docs; its imports are too
            published[m] = (pkg, path)
        else:
            sys.exit(f"error: cannot find the file of module {m}")
        todo += header_imports(path)
    return published


def git(repo, *args):
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                          text=True).stdout.strip()


def github_blob_base(repo):
    """`https://github.com/<org>/<repo>/blob/<commit>/` for the checkout `repo`, as doc-gen4 makes it."""
    url = git(repo, "remote", "get-url", "origin")
    if url.startswith("git@github.com:"):
        url = "https://github.com/" + url[len("git@github.com:"):]
    if not url.startswith("https://github.com/"):
        sys.exit(f"error: the origin remote of {repo} is {url}, not a GitHub repository, "
                 "so doc-gen4 can't link to its source")
    return f"{url.removesuffix('.git')}/blob/{git(repo, 'rev-parse', 'HEAD')}/"


def cmd_modules():
    bases, tops = {}, {}
    for name, (repo, path) in sorted(published_modules().items()):
        if repo not in bases:
            bases[repo] = github_blob_base(repo)
            tops[repo] = pathlib.Path(git(repo, "rev-parse", "--show-toplevel"))
        print(name, bases[repo] + path.resolve().relative_to(tops[repo]).as_posix())


def pinned_source(module, pkgs, manifest, lean_version):
    """The source file of an external `module` on GitHub, at the version SHSLib builds against."""
    parts = module.split(".")
    if parts[0] in LEAN_CORE:
        src = "src/lake/" if parts[0] == "Lake" else "src/"
        return f"https://github.com/leanprover/lean4/blob/{lean_version}/{src}{'/'.join(parts)}.lean"
    if module not in pkgs:
        return None
    pkg, path = pkgs[module]
    entry = manifest.get(pkg.name)
    if entry is None:
        return None
    return f"{entry['url'].removesuffix('.git')}/blob/{entry['rev']}/{path.relative_to(pkg).as_posix()}"


def load_mathlib_docs_index():
    url = MATHLIB_DOCS + "declarations/declaration-data.bmp"
    try:
        with urllib.request.urlopen(url, timeout=300) as response:
            data = json.load(response)
        return data["declarations"], data["modules"]
    except Exception as e:  # any failure: fall back to the find page, never fail the build
        print(f"warning: could not load {url} ({e}); declaration links will go through the find page",
              file=sys.stderr)
        return None


def cmd_link(doc_dir, offline):
    doc = pathlib.Path(doc_dir).resolve()
    published = set(published_modules())
    pkgs = package_modules()
    manifest = {p["name"]: p for p in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]}
    lean_version = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
    index = None if offline else load_mathlib_docs_index()
    if index is None:
        print("Linking declarations through the find page of the Mathlib documentation")
    kinds, to_source, errors = collections.Counter(), [], []

    def external(module, decl):
        """The URL replacing a link to `module` (and declaration `decl`, if any)."""
        if module.split(".")[0] not in LEAN_CORE and module not in pkgs:
            return None
        if index is None:
            if decl:
                kinds["declaration, through the find page"] += 1
                return f"{MATHLIB_DOCS}find/?pattern={urllib.parse.quote(decl, safe='')}#doc"
            kinds["module page, unchecked"] += 1
            return MATHLIB_DOCS + module.replace(".", "/") + ".html"
        decls, mods = index
        if decl and decl in decls:
            kinds["declaration page"] += 1
            return MATHLIB_DOCS + decls[decl]["docLink"].removeprefix("./")
        if not decl and module in mods:
            kinds["module page"] += 1
            return MATHLIB_DOCS + module.replace(".", "/") + ".html"
        url = pinned_source(module, pkgs, manifest, lean_version)
        if url:
            kinds["source at the pinned version"] += 1
            to_source.append(decl or module)
        return url

    for page in sorted(doc.rglob("*.html")):
        rel_dir = posixpath.dirname(page.relative_to(doc).as_posix())
        text = page.read_text(encoding="utf-8")

        def rewrite(m):
            raw = m.group(1)
            if not raw or raw.startswith(("#", "/")) or SCHEME.match(raw):
                return m.group(0)
            value = html.unescape(raw)
            path, _, decl = value.partition("#")
            path = path.split("?", 1)[0]
            target = posixpath.normpath(posixpath.join(rel_dir, path))
            if target.startswith("..") or (doc / target).is_file() or (doc / target / "index.html").is_file():
                return m.group(0)
            module = target.removesuffix(".html").replace("/", ".")
            url = None if module in published else external(module, decl)
            if url is None:
                errors.append(f"{page.relative_to(doc)}: {raw}")
                return m.group(0)
            return f'href="{html.escape(url, quote=True)}"'

        new = HREF.sub(rewrite, text)
        if new != text:
            page.write_text(new, encoding="utf-8")

    for kind, n in sorted(kinds.items()):
        print(f"{n:7d} links to a {kind}")
    if to_source:
        names = sorted(set(to_source))
        print(f"Not in the Mathlib documentation any more, linked to their source instead: {', '.join(names)}")
    if errors:
        print(f"error: {len(errors)} links point to pages that don't exist:", file=sys.stderr)
        print("\n".join("  " + e for e in errors[:20]), file=sys.stderr)
        sys.exit(1)


def cmd_check(doc_dir):
    doc = pathlib.Path(doc_dir)
    problems = [f"no page for module {m}" for m in published_modules()
                if not (doc / (m.replace(".", "/") + ".html")).is_file()]
    keys = re.findall(r"@\w+\s*\{\s*([^,\s]+)\s*,", (ROOT / "references.bib").read_text(encoding="utf-8"))
    page = (doc / "references.html").read_text(encoding="utf-8")
    problems += [f"references.html has no entry {k}" for k in keys if f'id="ref_{k}"' not in page]
    if problems:
        sys.exit("error: " + "\n       ".join(problems))
    print(f"All {len(published_modules())} module pages present; references.html lists all "
          f"{len(keys)} references.bib entries")


def main(argv):
    if argv[:1] == ["modules"] and len(argv) == 1:
        cmd_modules()
    elif argv[:1] == ["link"] and len(argv) in (2, 3) and argv[2:] in ([], ["--offline"]):
        cmd_link(argv[1], offline=argv[2:] == ["--offline"])
    elif argv[:1] == ["check"] and len(argv) == 2:
        cmd_check(argv[1])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
