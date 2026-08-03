param(
    [string]$ExperimentId = "stage_a_v3_mock_$(Get-Date -Format 'yyyyMMdd_HHmmss')"
)

$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..\..\..")
$cliPath = Join-Path $repoRoot "experiments/eight_c_goodness_pilot/scripts/ti_sigma_stage_a_v3_cli.py"
$gateRoot = Join-Path $repoRoot "experiments/eight_c_goodness_pilot/results/gate_runs/$ExperimentId"
$stepLogPath = Join-Path $gateRoot "gate_steps.jsonl"
$helpOutPath = Join-Path $gateRoot "cli_help.txt"

New-Item -ItemType Directory -Force -Path $gateRoot | Out-Null

function Invoke-Step {
    param(
        [string]$Name,
        [string]$Exe,
        [string[]]$Args
    )

    $timestamp = (Get-Date).ToUniversalTime().ToString("o")
    $commandLine = "$Exe " + ($Args -join " ")

    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = $Exe
    $psi.Arguments = ($Args -join " ")
    $psi.WorkingDirectory = $repoRoot.Path
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.UseShellExecute = $false
    $psi.CreateNoWindow = $true

    $proc = New-Object System.Diagnostics.Process
    $proc.StartInfo = $psi
    [void]$proc.Start()
    $stdout = $proc.StandardOutput.ReadToEnd()
    $stderr = $proc.StandardError.ReadToEnd()
    $proc.WaitForExit()
    $exitCode = $proc.ExitCode

    $stepRecord = [ordered]@{
        step = $Name
        command = $commandLine
        timestamp_utc = $timestamp
        exit_code = $exitCode
        stdout = $stdout
        stderr = $stderr
    }
    Add-Content -Path $stepLogPath -Value (($stepRecord | ConvertTo-Json -Depth 6 -Compress))

    if ($stdout) { Write-Output $stdout.TrimEnd() }
    if ($stderr) { Write-Output ("STDERR: " + $stderr.TrimEnd()) }

    if ($exitCode -ne 0) {
        throw "Step '$Name' failed with exit code $exitCode"
    }
}

# Save full CLI help output.
Invoke-Step -Name "cli-help" -Exe "python" -Args @($cliPath, "--help")
$helpJson = Get-Content -Path $stepLogPath | Select-Object -Last 1 | ConvertFrom-Json
$helpJson.stdout | Set-Content -Path $helpOutPath -Encoding UTF8

Invoke-Step -Name "tests" -Exe "python" -Args @("-m", "unittest", "discover", "experiments/eight_c_goodness_pilot/tests")
Invoke-Step -Name "freeze-check" -Exe "python" -Args @($cliPath, "freeze-check", "--strict")
Invoke-Step -Name "corpus-summary" -Exe "python" -Args @($cliPath, "corpus-summary")
Invoke-Step -Name "collection-check" -Exe "python" -Args @($cliPath, "collection-check", "--mock")
Invoke-Step -Name "cost-estimate" -Exe "python" -Args @($cliPath, "cost-estimate", "--mock")
Invoke-Step -Name "run" -Exe "python" -Args @($cliPath, "run", "--mock", "--experiment-id", $ExperimentId)
Invoke-Step -Name "validate" -Exe "python" -Args @($cliPath, "validate", "--experiment-id", $ExperimentId)
Invoke-Step -Name "seal" -Exe "python" -Args @($cliPath, "seal", "--experiment-id", $ExperimentId)
Invoke-Step -Name "report" -Exe "python" -Args @($cliPath, "report", "--experiment-id", $ExperimentId)
Invoke-Step -Name "manifest-verification" -Exe "python" -Args @($cliPath, "freeze-check", "--strict")
Invoke-Step -Name "seal-verification" -Exe "python" -Args @($cliPath, "seal", "--experiment-id", $ExperimentId, "--verify")

$terminalManifestPath = Join-Path $repoRoot "experiments/eight_c_goodness_pilot/results/experiments/$ExperimentId/terminal_manifest.json"
$terminal = Get-Content -Path $terminalManifestPath -Raw | ConvertFrom-Json

Write-Output "============================================================"
Write-Output "TI SIGMA EIGHT-C - STAGE A V3 MOCK RELEASE GATE"
Write-Output "============================================================"
Write-Output "Tests: PASS"
Write-Output "Freeze check: PASS"
Write-Output "Corpus summary: PASS"
Write-Output "Collection check: PASS"
Write-Output "Cost estimate: PASS"
Write-Output "Mock run: PASS"
Write-Output "Validation: PASS"
Write-Output "Seal: PASS"
Write-Output "Report: PASS"
Write-Output "Manifest verification: PASS"
Write-Output "Seal verification: PASS"
Write-Output ""
Write-Output "Items: 21"
Write-Output "Ratings per item: 3"
Write-Output "Planned logical ratings: $($terminal.planned_logical_ratings)"
Write-Output "Completed logical ratings: $($terminal.logical_ratings_completed)"
Write-Output "Valid logical ratings: $($terminal.logical_ratings_valid)"
Write-Output "Invalid-terminal: $($terminal.logical_ratings_invalid_terminal)"
Write-Output "Failed-terminal: $($terminal.logical_ratings_failed_terminal)"
Write-Output "Maximum attempts per logical rating: $($terminal.maximum_permitted_attempts_per_logical_rating)"
Write-Output "Maximum total attempts: $($terminal.maximum_total_attempts)"
Write-Output "Terminal state: $($terminal.terminal_state)"
Write-Output ""
Write-Output "Synthetic engineering data: YES"
Write-Output "Paid API requests: 0"
Write-Output "STAGE_A_V3_MOCK_GATE: PASS"
Write-Output "============================================================"