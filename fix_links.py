import re

# --- Customize this section ---
GITHUB_REPO = "dozenalist/Partitions-mod-p"
COMMIT_HASH = "ae225b168cfa378e0c0bd079d9e842d37f849c54"  # Replace with your actual commit
LEAN_PATH = "PartitionsLeanblueprint"  # Replace with the path to your Lean files

# Map from declaration name to (file, line number)
DECLARATION_LINKS = {
    "convergesTo": ("IVT.lean", 4),
    "converges": ("IVT.lean", 12),
    "myTheorem": ("Section1.lean", 23),
    # Add more entries as needed
}

# --- Processing ---

def github_url(decl_name):
    if decl_name not in DECLARATION_LINKS:
        return None
    file, line = DECLARATION_LINKS[decl_name]
    return f"https://github.com/{GITHUB_REPO}/blob/{COMMIT_HASH}/{LEAN_PATH}/{file}#L{line}"

def patch_index_html(file_path="docs/index.html"):
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    def replacer(match):
        decl = match.group(1)
        url = github_url(decl)
        if url:
            return f'href="{url}"'
        else:
            print(f"⚠️  No GitHub link found for '{decl}', leaving it unchanged.")
            return match.group(0)

    new_content = re.sub(r'href="#doc/(\w+)"', replacer, content)

    with open(file_path, "w", encoding="utf-8") as f:
        f.write(new_content)

    print("✅ Links patched in docs/index.html")

if __name__ == "__main__":
    patch_index_html()
