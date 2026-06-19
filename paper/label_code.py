# FILENAME: paper/label_code.py

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
    decl_regex = re.compile(r'^((?:noncomputable\s+)?(?:theorem|def|class|structure|instance|abbrev|lemma)\s+)([a-zA-Z0-9_.]+)')

    with open(OUTPUT_FILE, 'w', encoding='utf-8') as f:
        for line in lines:
            mod_match = mod_regex.match(line)
            if mod_match:
                current_module = mod_match.group(1)
            
            decl_match = decl_regex.match(line)
            if decl_match and current_module:
                prefix = decl_match.group(1)
                name = decl_match.group(2)
                
                # Ensure the name is fully qualified with the module path
                if name.startswith(current_module):
                    full_name = name
                else:
                    full_name = f"{current_module}.{name}"
                
                # Extract the BibTeX key if this is a Litlib module
                cite_str = ""
                if current_module.startswith("Litlib.Y"):
                    parts = current_module.split('.')
                    if len(parts) >= 3:
                        bib_key = parts[2]
                        # Use \textsuperscript so the citation doesn't look like a Lean array index [1]
                        cite_str = f"§\\textsuperscript{{\\cite{{{bib_key}}}}}§"

                # Injects the FULL name so the module prefix is visually printed in the PDF
                remainder = line[decl_match.end():]
                f.write(f"{prefix}§\\phantomsection\\label{{lean:{full_name}}}§{full_name}{cite_str}{remainder}")
            else:
                f.write(line)

    print(f"Generated {OUTPUT_FILE} with bulletproof hyperlinked labels and inline citations!")

if __name__ == "__main__":
    main()
