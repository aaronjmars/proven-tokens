"""Build the `lean-ethlib` E2B template: base image + elan + Lean v4.35.0.
Usage: E2B_API_KEY=... python3 build_template.py <cpu> <memory_mb> [name]
"""
import sys
from e2b import Template, default_build_logger

cpu, mem = int(sys.argv[1]), int(sys.argv[2])
name = sys.argv[3] if len(sys.argv) > 3 else "lean-ethlib"
template = (
    Template()
    .from_base_image()
    .run_cmd("curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"
             " | sh -s -- -y --default-toolchain leanprover/lean4:v4.35.0"
             " && $HOME/.elan/bin/lean --version")
)
info = Template.build(template, name, cpu_count=cpu, memory_mb=mem,
                      on_build_logs=default_build_logger())
print("BUILT", info)
