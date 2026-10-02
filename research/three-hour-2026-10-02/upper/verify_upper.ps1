param(
    [string]$CompilerRunner = '',
    [string[]]$OnlyModules = @()
)

# Run from any directory. The repository's lean-toolchain and lake manifest
# select the pinned Lean/Mathlib versions. CompilerRunner is optional local
# scheduling glue; the default requires only the normal `lake` executable.
$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
$logDir = Join-Path $PSScriptRoot 'verification'
$null = New-Item -ItemType Directory -Force -Path $logDir
$modules = @(
    'UpperFan',
    'UpperSharedEdge',
    'UpperFanSupport',
    'UpperCoreBoundary',
    'UpperCoreBudget',
    'UpperElementaryEdges',
    'UpperEdgeCapacity',
    'UpperTriangleIncidence',
    'UpperSharedIncidence',
    'UpperVertexBudget',
    'UpperEdgeInventory',
    'UpperCoreExtraction',
    'UpperCoreLineIncidence',
    'UpperCoreCombinatorics',
    'UpperTripleFan',
    'UpperCleanHalfplane',
    'UpperCleanEdges',
    'UpperCleanPairing',
    'UpperCleanCover',
    'UpperCleanCharging'
)
$reportName = 'summary.json'
if ($OnlyModules.Count -gt 0) {
    foreach ($requested in $OnlyModules) {
        if ($requested -notin $modules) { throw "Unknown upper module: $requested" }
    }
    $modules = @($modules | Where-Object { $_ -in $OnlyModules })
    $reportName = 'summary-supplement.json'
}
$records = @()
$overallPass = $true
Push-Location $repoRoot
try {
    foreach ($module in $modules) {
        $source = "Kobon/$module.lean"
        $output = ".lake/build/lib/lean/Kobon/$module.olean"
        $sourceText = Get-Content -Raw -LiteralPath $source
        $forbidden = [regex]::IsMatch($sourceText, '\b(sorry|admit|axiom|unsafe)\b')
        $started = [DateTime]::UtcNow.ToString('o')
        $timer = [Diagnostics.Stopwatch]::StartNew()
        if ($CompilerRunner) {
            $result = & $CompilerRunner -LakeArgs @('env', 'lean', '-o', $output, $source) 2>&1 | Out-String
        } else {
            $result = & lake env lean -o $output $source 2>&1 | Out-String
        }
        $exitCode = $LASTEXITCODE
        $timer.Stop()
        $logPath = Join-Path $logDir "$module.log"
        Set-Content -Encoding utf8 -LiteralPath $logPath -Value $result
        $axiomLists = [regex]::Matches($result, 'depends on axioms:\s*\[([^\]]*)\]')
        $unexpectedAxioms = @($axiomLists | ForEach-Object {
            $_.Groups[1].Value.Split(',') | ForEach-Object { $_.Trim() } |
                Where-Object { $_ -and $_ -notin @('propext', 'Classical.choice', 'Quot.sound') }
        } | Select-Object -Unique)
        $badAxiom = $unexpectedAxioms.Count -gt 0
        $passed = ($exitCode -eq 0) -and (-not $forbidden) -and (-not $badAxiom) -and ($axiomLists.Count -gt 0)
        $records += [ordered]@{
            module = "Kobon.$module"
            source = $source
            sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $source).Hash.ToLowerInvariant()
            started_utc = $started
            elapsed_seconds = [math]::Round($timer.Elapsed.TotalSeconds, 3)
            compiler_exit_code = $exitCode
            forbidden_source_marker = $forbidden
            forbidden_axiom_output = $badAxiom
            printed_axiom_roots = $axiomLists.Count
            unexpected_axioms = $unexpectedAxioms
            passed = $passed
            log = "verification/$module.log"
        }
        Write-Output "$module : $passed"
        if (-not $passed) {
            $overallPass = $false
            break
        }
    }
    $report = [ordered]@{
        generated_utc = [DateTime]::UtcNow.ToString('o')
        description = 'Sequential pinned-Lean compilation and printed-root axiom audit; source marker check is additional, not a substitute for kernel checking.'
        modules_expected = $modules.Count
        modules_checked = $records.Count
        passed = $overallPass -and ($records.Count -eq $modules.Count)
        results = $records
    }
    $report | ConvertTo-Json -Depth 8 | Set-Content -Encoding utf8 -LiteralPath (Join-Path $logDir $reportName)
} finally {
    Pop-Location
}
if (-not $overallPass) { exit 1 }
