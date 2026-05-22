import os
import glob
import subprocess
import re

moves = {
    # Core
    "Echo": "Echo.Core",
    "EchoCharacteristic": "Echo.Characteristic",
    "EchoResidue": "Echo.Residue",
    
    # Bridges
    "EchoGradedComonad": "Echo.Bridges.EchoGradedComonad",
    "EchoGradedComonadF1": "Echo.Bridges.EchoGradedComonadF1",
    "EchoGradedComonadInterface": "Echo.Bridges.EchoGradedComonadInterface",
    "EchoGradedComonadInstance1": "Echo.Bridges.EchoGradedComonadInstance1",
    "EchoGradedComonadInstance2": "Echo.Bridges.EchoGradedComonadInstance2",
    "EchoGraded": "Echo.Bridges.EchoGraded",
    
    "EchoThermodynamics": "Echo.Bridges.EchoThermodynamics",
    "EchoThermodynamicsArbitrary": "Echo.Bridges.EchoThermodynamicsArbitrary",
    "EchoThermodynamicsFinite": "Echo.Bridges.EchoThermodynamicsFinite",
    "EchoThermoCollapseImpossible": "Echo.Bridges.EchoThermoCollapseImpossible",
    
    "EchoCNOBridge": "Echo.Bridges.EchoCNOBridge",
    "MinimalCNO": "Echo.Bridges.MinimalCNO",
    "WorkingCNO": "Echo.Bridges.WorkingCNO",
    
    "EchoJanusBridge": "Echo.Bridges.EchoJanusBridge",
    
    "EchoCategorical": "Echo.Bridges.EchoCategorical",
    "EchoRelational": "Echo.Bridges.EchoRelational",
    "EchoRelModel": "Echo.Bridges.EchoRelModel",
    "EchoIndexed": "Echo.Bridges.EchoIndexed",
    "EchoScope": "Echo.Bridges.EchoScope",
    "EchoPullback": "Echo.Bridges.EchoPullback",
    "EchoPullbackUnivF4": "Echo.Bridges.EchoPullbackUnivF4",
    "EchoSeparating": "Echo.Bridges.EchoSeparating",
    
    "EchoTropical": "Echo.Bridges.EchoTropical",
    "AntiEcho": "Echo.Bridges.AntiEcho",
    "AntiEchoTropical": "Echo.Bridges.AntiEchoTropical",
    "AntiEchoTropicalGeneric": "Echo.Bridges.AntiEchoTropicalGeneric",
    
    "Dyadic": "Echo.Bridges.Dyadic",
    "DyadicEchoBridge": "Echo.Bridges.DyadicEchoBridge",
    "EchoOrdinal": "Echo.Bridges.EchoOrdinal",
    
    "EchoStepNDModelF2": "Echo.Bridges.EchoStepNDModelF2",
    "EchoFiberBridge": "Echo.Bridges.EchoFiberBridge",

    # Examples
    "EchoExampleAbsInt": "Echo.Examples.EchoExampleAbsInt",
    "EchoExampleParser": "Echo.Examples.EchoExampleParser",
    "EchoExampleProvenance": "Echo.Examples.EchoExampleProvenance",
    "EchoExamples": "Echo.Examples.EchoExamples",
    "EchoExampleSignAnalysis": "Echo.Examples.EchoExampleSignAnalysis",
    "EchoExampleTruncation": "Echo.Examples.EchoExampleTruncation",
    "EchoSearchExample": "Echo.Examples.EchoSearchExample",
    
    # Others
    "EchoAccess": "Echo.Bridges.EchoAccess",
    "EchoApprox": "Echo.Bridges.EchoApprox",
    "EchoApproxInstance": "Echo.Bridges.EchoApproxInstance",
    "EchoChoreo": "Echo.Bridges.EchoChoreo",
    "EchoCost": "Echo.Bridges.EchoCost",
    "EchoCostInstance": "Echo.Bridges.EchoCostInstance",
    "EchoDecidable": "Echo.Bridges.EchoDecidable",
    "EchoEpistemic": "Echo.Bridges.EchoEpistemic",
    "EchoEpistemicResidue": "Echo.Bridges.EchoEpistemicResidue",
    "EchoFiberCount": "Echo.Bridges.EchoFiberCount",
    "EchoFiberTriangulation": "Echo.Bridges.EchoFiberTriangulation",
    "EchoIntegration": "Echo.Bridges.EchoIntegration",
    "EchoSearch": "Echo.Bridges.EchoSearch",
    "EchoSearchInstance": "Echo.Bridges.EchoSearchInstance",
    "EchoStabilityTests": "Echo.Bridges.EchoStabilityTests",
    "EchoTruncation": "Echo.Bridges.EchoTruncation",
    
    # Let's add EchoKernel as Core? The instructions don't say to move EchoKernel.
}

agda_files = glob.glob("proofs/agda/**/*.agda", recursive=True)

# Generate list of renames
for old_mod, new_mod in moves.items():
    old_path = "proofs/agda/" + old_mod.replace(".", "/") + ".agda"
    new_path = "proofs/agda/" + new_mod.replace(".", "/") + ".agda"
    
    if os.path.exists(old_path):
        os.makedirs(os.path.dirname(new_path), exist_ok=True)
        subprocess.run(["git", "mv", old_path, new_path], check=True)
    else:
        print(f"Warning: {old_path} not found")

# Refresh list of agda files after move
agda_files = glob.glob("proofs/agda/**/*.agda", recursive=True)

for file_path in agda_files:
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()
    
    new_content = content
    # To prevent partial matches, process longer names first, and ensure word boundaries exclude dots.
    for old_mod, new_mod in sorted(moves.items(), key=lambda x: -len(x[0])):
        pattern_mod = r'(?<!\.)\bmodule\s+' + re.escape(old_mod) + r'\b(?!\.)'
        pattern_imp = r'(?<!\.)\bimport\s+' + re.escape(old_mod) + r'\b(?!\.)'
        pattern_opn = r'(?<!\.)\bopen\s+' + re.escape(old_mod) + r'\b(?!\.)'
        
        new_content = re.sub(pattern_mod, f'module {new_mod}', new_content)
        new_content = re.sub(pattern_imp, f'import {new_mod}', new_content)
        new_content = re.sub(pattern_opn, f'open {new_mod}', new_content)

    if new_content != content:
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(new_content)

print("Refactoring complete.")
