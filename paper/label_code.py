import os
import re

INPUT_FILE = "code-summary.txt"
OUTPUT_FILE = "code-summary-labeled.txt"

def main():
    if not os.path.exists(INPUT_FILE):
        print(f"Error: {INPUT_FILE} not found.")
        return

    with open(INPUT_FILE, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    current_module = ""
    mod_regex = re.compile(r'^-- MODULE:\s*(\S+)')
    # Captures the keyword prefix (Group 1) and the full theorem name including dots/underscores (Group 2)
    decl_regex = re.compile(r'^((?:noncomputable\s+)?(?:theorem|def|class|structure|instance|abbrev)\s+)([a-zA-Z0-9_.]+)')

    with open(OUTPUT_FILE, 'w', encoding='utf-8') as f:
        for line in lines:
            mod_match = mod_regex.match(line)
            if mod_match:
                current_module = mod_match.group(1)
            
            decl_match = decl_regex.match(line)
            if decl_match and current_module:
                prefix = decl_match.group(1)
                name = decl_match.group(2)
                full_name = f"{current_module}.{name}"
                # Injects: theorem |\label{lean:Module.Name}| Name ...
                remainder = line[decl_match.end():]
                f.write(f"{prefix}|\\phantomsection\\label{{lean:{full_name}}}|{name}{remainder}")
            else:
                f.write(line)

    print(f"Generated {OUTPUT_FILE} with bulletproof hyperlinked labels!")

if __name__ == "__main__":
    main()
