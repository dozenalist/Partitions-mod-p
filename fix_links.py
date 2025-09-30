import os
import re

# === Configuration ===
GITHUB_REPO = "dozenalist/Partitions-mod-p"
COMMIT_HASH = "main"  # Use 'main' if preferred
LEAN_DECLS_PATH = "blueprint/lean_decls"
LEAN_SOURCE_DIR = "PartitionsLeanblueprint"  # Change if your .lean files live elsewhere
PROJECT_ROOT = "."  # Replace with the path to your root directory if needed

# === Step 1: Load declaration names from lean_decls ===
with open(LEAN_DECLS_PATH, "r", encoding="utf-8") as f:
    decl_names = [line.strip() for line in f if line.strip()]

decl_names = [name.split(".")[-1] for name in decl_names]

# === Step 2: Find declarations in .lean files ===
decl_lookup = {}

decl_lookup = {}

for root, _, files in os.walk(LEAN_SOURCE_DIR):
    for file in files:
        if not file.endswith(".lean"):
            continue
        full_path = os.path.join(root, file)
        rel_path = os.path.relpath(full_path, start=PROJECT_ROOT)
        with open(full_path, "r", encoding="utf-8") as f:
            namespace_stack = []
            for i, line in enumerate(f, start=1):
                # Track namespace nesting
                ns_match = re.match(r"\s*namespace\s+([\w\.]+)", line)
                if ns_match:
                    namespace_stack.append(ns_match.group(1))
                if re.match(r"\s*end\b", line):
                    if namespace_stack:
                        namespace_stack.pop()

                # Look for theorem/lemma/def lines
                m = re.match(r"\s*(?:private|scoped|noncomputable\s+)*\s*(theorem|def|lemma)\s+(\w+)", line)
                if m:
                    kind, name = m.groups()
                    fq_name = ".".join(namespace_stack + [name]) if namespace_stack else name
                    url = (
                        f"https://github.com/{GITHUB_REPO}/blob/{COMMIT_HASH}/"
                        f"{rel_path.replace(os.sep, '/')}"
                        f"#L{i}"
                    )
                    # Save both short and fully qualified
                    decl_lookup[name] = url
                    decl_lookup[fq_name] = url


print(f"🔍 Found source locations for {len(decl_lookup)} declarations")

# === Step 3: Patch all .html files in the project ===
html_files_patched = 0
link_pattern = r'href="https://github\.com/[^/]+/[^/]+/find/#doc/([\w\.]+)"'

for root, _, files in os.walk(PROJECT_ROOT):
    for file in files:
        if not file.endswith(".html"):
            continue
        full_path = os.path.join(root, file)
        with open(full_path, "r", encoding="utf-8") as f:
            content = f.read()

        def replacer(match):
            name = match.group(1)
            if name in decl_lookup:
                return f'href="{decl_lookup[name]}"'
            else:
                print(f"⚠️ No GitHub link found for '{name}', leaving it unchanged.")
                return match.group(0)

        new_content = re.sub(link_pattern, replacer, content)

        if new_content != content:
            with open(full_path, "w", encoding="utf-8") as f:
                f.write(new_content)
            print(f"✅ Patched links in {full_path}")
            html_files_patched += 1

print(f"\n✨ Done. Patched {html_files_patched} HTML file(s).")
