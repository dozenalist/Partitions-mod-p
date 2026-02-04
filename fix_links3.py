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
    raw_decl_lines = [line.strip() for line in f if line.strip()]

# Keep both the raw entries (may contain dots) and the set of short names
decls_raw = set(raw_decl_lines)
decls_shorts = set(r.split(".")[-1] for r in raw_decl_lines)

# === Step 2: Find declarations in .lean files ===
decl_lookup = {}

for root, _, files in os.walk(LEAN_SOURCE_DIR):
    for file in files:
        if not file.endswith(".lean"):
            continue
        full_path = os.path.join(root, file)
        rel_path = os.path.relpath(full_path, start=PROJECT_ROOT)
        with open(full_path, "r", encoding="utf-8") as f:
            ns_stack = []
            for i, line in enumerate(f, start=1):
                # track namespace openings
                ns_match = re.match(r"\s*namespace\s+([\w\.]+)", line)
                if ns_match:
                    parts = ns_match.group(1).split('.')
                    ns_stack.extend(parts)
                    continue

                # track namespace ends (pop only when it matches)
                end_match = re.match(r"\s*end(?:\s+([\w\.]+))?", line)
                if end_match:
                    if end_match.group(1):
                        if ns_stack and ns_stack[-1] == end_match.group(1):
                            ns_stack.pop()
                    else:
                        if ns_stack:
                            ns_stack.pop()
                    continue

                # Look for declarations. Allow dots/apostrophes in the "name" token
                m = re.match(
                    r"\s*(?:@\[[^\]]*\]\s*)*(?:private|scoped|protected|noncomputable\s+)*\s*"
                    r"(theorem|def|lemma|structure|class|inductive|abbrev)\s+([A-Za-z0-9_\.']+)",
                    line
                )
                if not m:
                    continue

                kind, name = m.groups()
                # short form (last component after any dot)
                short_name = name.split('.')[-1]
                fq_name = ".".join(ns_stack + [name]) if ns_stack else name

                # ONLY register declarations that exactly match an entry in lean_decls
                # Match if the raw name equals an entry, OR fq_name equals an entry, OR short_name equals an entry
                if not (name in decls_raw or fq_name in decls_raw or short_name in decls_shorts):
                    # skip anything not explicitly requested
                    continue

                url = (
                    f"https://github.com/{GITHUB_REPO}/blob/{COMMIT_HASH}/"
                    f"{rel_path.replace(os.sep, '/')}"
                    f"#L{i}"
                )

                # store the fully qualified form (if applicable) and the exact name found
                decl_lookup[fq_name] = url
                decl_lookup[name] = url
                # store short form only if it's not ambiguous (we keep it anyway but exact-match fallback is used below)
                if short_name not in decl_lookup:
                    decl_lookup[short_name] = url

print(f"🔍 Found source locations for {len(decl_lookup)} recorded name entries")

# === Step 3: Patch all .html files in the project ===
html_files_patched = 0
link_pattern = re.compile(r'''href="https://github\.com/[^/]+/[^/]+/find/#doc/([\w\.']+)"''')

for root, _, files in os.walk(PROJECT_ROOT):
    for file in files:
        if not file.endswith(".html"):
            continue
        full_path = os.path.join(root, file)
        with open(full_path, "r", encoding="utf-8") as f:
            content = f.read()

        def replacer(match):
            raw = match.group(1)  # e.g. "Final.Hidden.alpha" or "ModularForm.ext" or "alpha"
            # Prefer exact raw match (which may be fq or dotted)
            if raw in decl_lookup:
                return f'href="{decl_lookup[raw]}"'

            # If not exact, try exact short-name match (only if unambiguous)
            short = raw.split(".")[-1]
            # gather unique URLs for keys that exactly equal the short name
            exact_short_matches = [url for key, url in decl_lookup.items() if key == short]
            if len(exact_short_matches) == 1:
                return f'href="{exact_short_matches[0]}"'

            # Final fallback: if there is exactly one fq entry that ends with ".short", use it
            suffix_matches = [url for key, url in decl_lookup.items() if key.endswith("." + short)]
            if len(suffix_matches) == 1:
                return f'href="{suffix_matches[0]}"'

            # ambiguous or not found — leave unchanged
            print(f"⚠️ No unambiguous GitHub link found for '{raw}', leaving it unchanged.")
            return match.group(0)

        new_content = link_pattern.sub(replacer, content)

        if new_content != content:
            with open(full_path, "w", encoding="utf-8") as f:
                f.write(new_content)
            print(f"✅ Patched links in {full_path}")
            html_files_patched += 1

print(f"\n✨ Done. Patched {html_files_patched} HTML file(s).")

