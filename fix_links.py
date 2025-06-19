import os
import re

# === Configuration ===
GITHUB_REPO = "dozenalist/Partitions-mod-p"
COMMIT_HASH = "ae225b168cfa378e0c0bd079d9e842d37f849c54"  # or 'main'
LEAN_DECLS_PATH = "blueprint/lean_decls"
LEAN_SOURCE_DIR = "PartitionsLeanblueprint"  # adjust if your .lean files live elsewhere
INDEX_HTML_PATH = "docs/index.html"

# === Step 1: Load theorem names ===
with open(LEAN_DECLS_PATH, "r", encoding="utf-8") as f:
    decl_names = [line.strip() for line in f if line.strip()]

# === Step 2: Find declarations in .lean files ===
decl_lookup = {}

for root, _, files in os.walk(LEAN_SOURCE_DIR):
    for file in files:
        if not file.endswith(".lean"):
            continue
        path = os.path.join(root, file)
        rel_path = os.path.relpath(path, start=".")
        with open(path, "r", encoding="utf-8") as f:
            for i, line in enumerate(f, start=1):
                for name in decl_names:
                    # Look for `theorem name`, `def name`, or `lemma name`
                    if re.match(rf"\s*(theorem|def|lemma)\s+{re.escape(name)}\b", line):
                        if name not in decl_lookup:
                            decl_lookup[name] = f"https://github.com/{GITHUB_REPO}/blob/{COMMIT_HASH}/{rel_path.replace(os.sep, '/')}" + f"#L{i}"

# === Step 3: Patch index.html ===
with open(INDEX_HTML_PATH, "r", encoding="utf-8") as f:
    html = f.read()

def replacer(match):
    name = match.group(1)
    if name in decl_lookup:
        return f'href="{decl_lookup[name]}"'
    else:
        print(f"⚠️ Could not find declaration '{name}', leaving as-is.")
        return match.group(0)

html = re.sub(r'href="#doc/(\w+)"', replacer, html)

with open(INDEX_HTML_PATH, "w", encoding="utf-8") as f:
    f.write(html)

print(f"✅ Patched links for {len(decl_lookup)} declarations in index.html.")
