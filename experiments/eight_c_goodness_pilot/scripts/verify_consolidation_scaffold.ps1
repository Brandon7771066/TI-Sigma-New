$ErrorActionPreference = "Stop"

function Get-GitOutput {
    param([string]$Command)
    return (Invoke-Expression $Command 2>$null)
}

$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$pilotRoot = Resolve-Path (Join-Path $scriptRoot "..")
$repoRoot = Resolve-Path (Join-Path $pilotRoot "..\..")

$blockers = New-Object System.Collections.Generic.List[string]

Push-Location $repoRoot
try {
    $remote = Get-GitOutput "git remote get-url origin"
    $branch = Get-GitOutput "git rev-parse --abbrev-ref HEAD"
    $head = Get-GitOutput "git rev-parse HEAD"
    $aheadBehind = Get-GitOutput "git rev-list --left-right --count origin/main...HEAD"
    $scopedStatus = Get-GitOutput "git status --short -- experiments/eight_c_goodness_pilot docs/ti_sigma_framework"

    $requiredDirs = @(
        "experiments/eight_c_goodness_pilot",
        "experiments/eight_c_goodness_pilot/docs/provenance",
        "experiments/eight_c_goodness_pilot/docs/framework_sources/inbox",
        "experiments/eight_c_goodness_pilot/scripts"
    )

    $requiredFiles = @(
        "docs/ti_sigma_framework/canonical_definitions.md",
        "experiments/eight_c_goodness_pilot/docs/provenance/source_ledger.csv",
        "experiments/eight_c_goodness_pilot/docs/provenance/source_import_manifest.yaml",
        "experiments/eight_c_goodness_pilot/docs/provenance/reconstruction_plan.md",
        "experiments/eight_c_goodness_pilot/docs/provenance/consolidation_inventory.md"
    )

    foreach ($d in $requiredDirs) {
        if (-not (Test-Path $d -PathType Container)) {
            $blockers.Add("Missing required directory: $d")
        }
    }

    foreach ($f in $requiredFiles) {
        if (-not (Test-Path $f -PathType Leaf)) {
            $blockers.Add("Missing required file: $f")
        }
    }

    $canonicalPath = "docs/ti_sigma_framework/canonical_definitions.md"
    $concretenessExact = "Concreteness is the degree of tangibility or determinate intelligibility of the evaluated entity: how readily it can be understood, represented, or operationally grasped with minimal fuzziness, vagueness, or ambiguity."
    $boundaryExact = "Concreteness in GILE-G does not measure degree of ontological instantiation. Ontological instantiation belongs to HEM."

    $canonicalContent = ""
    if (Test-Path $canonicalPath -PathType Leaf) {
        $canonicalContent = Get-Content $canonicalPath -Raw
    }

    $hasConcreteness = $canonicalContent -like "*$concretenessExact*"
    $hasBoundary = $canonicalContent -like "*$boundaryExact*"

    if (-not $hasConcreteness) {
        $blockers.Add("Exact Concreteness definition not found in docs/ti_sigma_framework/canonical_definitions.md")
    }

    if (-not $hasBoundary) {
        $blockers.Add("Explicit GILE/HEM boundary statement not found in docs/ti_sigma_framework/canonical_definitions.md")
    }

    $stageAPath = ".github/workflows/stage-a-release-gate.yml"
    $stageAInTree = Get-GitOutput "git ls-tree -r --name-only HEAD | Select-String -Pattern '^\.github/workflows/stage-a-release-gate\.yml$'"
    $stageAExists = (Test-Path $stageAPath -PathType Leaf) -or ($null -ne $stageAInTree -and "$stageAInTree".Trim().Length -gt 0)
    if ($stageAExists) {
        $blockers.Add("Accidental Stage A workflow detected: .github/workflows/stage-a-release-gate.yml")
    }

    # Only scan source/provenance content locations to avoid self-matching this script text.
    $paidApiMatches = Select-String -Path @(
        "experiments/eight_c_goodness_pilot/docs/provenance/*",
        "experiments/eight_c_goodness_pilot/docs/framework_sources/inbox/*"
    ) -Pattern "api\.openai\.com|OPENAI_API_KEY|responses\.create|ChatCompletion" -ErrorAction SilentlyContinue
    $paidApiDetected = $null -ne $paidApiMatches
    if ($paidApiDetected) {
        $blockers.Add("Potential paid API marker detected under scaffold path.")
    }

    $remoteBranch = Get-GitOutput "git ls-remote --heads origin consolidation/eight-c-pilot"
    $pushDetected = $null -ne $remoteBranch -and "$remoteBranch".Trim().Length -gt 0
    if ($pushDetected) {
        $blockers.Add("Remote branch consolidation/eight-c-pilot exists; no-push condition violated.")
    }

    Write-Output "CONSOLIDATION_SCAFFOLD_VERIFICATION"
    Write-Output "repository_remote: $remote"
    Write-Output "branch: $branch"
    Write-Output "head_commit: $head"
    Write-Output "ahead_behind_vs_origin_main: $aheadBehind"
    Write-Output "scoped_git_status:"
    if ([string]::IsNullOrWhiteSpace($scopedStatus)) {
        Write-Output "  CLEAN"
    } else {
        $scopedStatus -split "`r?`n" | ForEach-Object { Write-Output "  $_" }
    }
    Write-Output "has_exact_concreteness_definition: $hasConcreteness"
    Write-Output "has_explicit_gile_hem_boundary: $hasBoundary"
    Write-Output "has_source_ledger: $(Test-Path 'experiments/eight_c_goodness_pilot/docs/provenance/source_ledger.csv' -PathType Leaf)"
    Write-Output "has_source_import_manifest: $(Test-Path 'experiments/eight_c_goodness_pilot/docs/provenance/source_import_manifest.yaml' -PathType Leaf)"
    Write-Output "has_reconstruction_plan: $(Test-Path 'experiments/eight_c_goodness_pilot/docs/provenance/reconstruction_plan.md' -PathType Leaf)"
    Write-Output "has_consolidation_inventory: $(Test-Path 'experiments/eight_c_goodness_pilot/docs/provenance/consolidation_inventory.md' -PathType Leaf)"
    Write-Output "stage_a_workflow_detected: $stageAExists"
    Write-Output "paid_api_marker_detected: $paidApiDetected"
    Write-Output "push_detected: $pushDetected"

    if ($blockers.Count -eq 0) {
        Write-Output "EIGHT_C_CONSOLIDATION_SCAFFOLD_READY: TRUE"
    } else {
        Write-Output "EIGHT_C_CONSOLIDATION_SCAFFOLD_READY: FALSE"
        Write-Output "BLOCKING_CONDITIONS:"
        foreach ($b in $blockers) {
            Write-Output "- $b"
        }
    }
}
finally {
    Pop-Location
}