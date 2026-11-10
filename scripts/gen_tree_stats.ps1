<#
=====================================================================
 gen_tree_stats.ps1 -- S7/PA4+PB6 full-tree module counter, tree-stats.json generator
 (ConstructiveWorld reinforcement SLICE-S7 tool item, tool family, zero compile / zero network / zero git write)
---------------------------------------------------------------------
 Six counting dimensions:
   1 full-tree .v     = side tree Live_X recursive *.v (all files)
   2 Live_X top level = side tree Live_X depth-0 *.v (sandbox-family subdirectories excluded by construction)
   3 UpAbl top level  = Live_X depth-0 name prefix UpAbl*.v
   4 attn sandbox     = Live_X\attn recursive *.v
   5 order lines      = order.txt physical line count (registered copies: main Live / side-tree Live / vo tree, scripts probed as well)
   6 commit face      = main repo git commit face: ConstructiveWorld_Live/*.v (repo-wide *.v attached separately)
 Three calibers, listed apart (PB6: registration face / side-tree top level / sandbox):
   A registration face = dimensions 5+6 (git commit face + order line counts)
   B side-tree top     = dimensions 2+3 -- paper citation caliber is FIXED to side-tree top level (dimension 2); the anti-rust statement is persisted with the JSON
   C sandbox           = dimension 4
 Reconciliation (fail-loud): embedded 09-22 two-pass manual ground truth --
   PR-B: Live_X top 841 / full 1402 / attn sandbox 363 / UpAbl top 226 / order 572 / commit face 609
   PR-C: Live_X top 839 / UpAbl top 226 / order 572 / commit face 609
   Any |measured-manual|/manual > 5% -> exit code 2, verdict "co-exist evidence, no forced judgment" (PRWO work-order red line).
 Usage:
   pwsh -File gen_tree_stats.ps1 -SelfTest          # run once on the current tree + reconciliation table (acceptance mode)
   pwsh -File gen_tree_stats.ps1 -TamperTest        # negative self-test: injected fake ground truth must trigger exit code 2
   pwsh -File gen_tree_stats.ps1 [-OutFile x.json] [-CI]   # regular output; -CI = runner resilience
 Territory: read-only statistics (repo tree/git read-only); the only write surface = -OutFile (default tree-stats.json beside this tool).
 coq.yml original untouched (CI #107 rerun in flight); CI consumes this tool once it lands in scripts/ with an R11x registration wave.
=====================================================================
#>
[CmdletBinding()]
param(
  [string]$SideTree = 'D:\ComplexAnalysis\新算法实践\Live_X',
  [string]$MainRepo = 'D:\ComplexAnalysis\ConstructiveWorld-Main',
  [string]$SideLive = 'D:\ComplexAnalysis\ConstructiveWorld_Live',
  [string]$VoTree   = 'D:\ComplexAnalysis\ConstructiveWorld_vo',
  [string]$OutFile  = '',
  [switch]$SelfTest,
  [switch]$TamperTest,
  [switch]$CI
)
$ErrorActionPreference = 'Stop'
$script:FailLoud = $false

# --- Counting primitives: filter '*.v' by Name afterwards (avoids -Filter 8.3 short-name false matches); read-only -----------------
function Count-V {
  param([string]$Dir, [switch]$Recurse)
  if ([string]::IsNullOrWhiteSpace($Dir) -or -not (Test-Path -LiteralPath $Dir)) { return $null }
  $gci = @{ LiteralPath = $Dir; File = $true; Force = $false }
  if ($Recurse) { $gci.Recurse = $true }
  @(Get-ChildItem @gci | Where-Object { $_.Name -like '*.v' }).Count
}
function Get-OrderLines {
  param([string[]]$Paths)
  $out = [ordered]@{}
  foreach ($p in $Paths) {
    if (Test-Path -LiteralPath $p) {
      $n = 0
      foreach ($l in [System.IO.File]::ReadLines($p)) { $n++ }
      $out[$p] = $n
    } else { $out[$p] = $null }
  }
  $out
}
function Get-GitFace {
  param([string]$Repo, [string]$Pathspec)
  try {
    $lines = @(& git -C $Repo ls-files -- $Pathspec 2>$null)
    if ($LASTEXITCODE -ne 0) { return $null }
    @($lines | Where-Object { $_ -match '\.v$' }).Count
  } catch { return $null }
}

# --- Six-dimension counts -------------------------------------------------------
$topFiles      = $null
$liveTop       = $null
if (Test-Path -LiteralPath $SideTree) {
  $topFiles = @(Get-ChildItem -LiteralPath $SideTree -File | Where-Object { $_.Name -like '*.v' })
  $liveTop  = $topFiles.Count
}
$fullTree      = Count-V $SideTree -Recurse
$attnSandbox   = Count-V (Join-Path $SideTree 'attn') -Recurse
$upablTop      = if ($null -ne $topFiles) { @($topFiles | Where-Object { $_.Name -like 'UpAbl*.v' }).Count } else { $null }
$upablRec      = $null
if (Test-Path -LiteralPath $SideTree) {
  $upablRec = @(Get-ChildItem -LiteralPath $SideTree -Recurse -File | Where-Object { $_.Name -like 'UpAbl*.v' }).Count
}
$orderLines    = Get-OrderLines @(
  (Join-Path $MainRepo 'ConstructiveWorld_Live\order.txt'),
  (Join-Path $SideLive 'order.txt'),
  (Join-Path $VoTree 'order.txt'),
  (Join-Path $MainRepo 'scripts\order.txt')
)
$orderVals     = @($orderLines.Values | Where-Object { $null -ne $_ })
$orderMax      = if ($orderVals.Count) { [int]($orderVals | Measure-Object -Maximum).Maximum } else { $null }
$orderMin      = if ($orderVals.Count) { [int]($orderVals | Measure-Object -Minimum).Minimum } else { $null }
$orderConsist  = if ($orderVals.Count -ge 2) { if ($orderMax -eq $orderMin) { 'three-way-consistent' } else { 'DIVERGED' } } else { 'insufficient-copies' }

$faceLiveDir   = Get-GitFace $MainRepo 'ConstructiveWorld_Live/*.v'
$faceRepoAll   = Get-GitFace $MainRepo '*.v'
$headNote      = $null
try {
  $h = & git -C $MainRepo log -1 --format='%h|%ad' --date=iso 2>$null
  if ($LASTEXITCODE -eq 0 -and $h) { $headNote = ($h -join '') }
} catch { $headNote = $null }

# --- Reconciliation ground truth (09-22 PR-B/PR-C manual) and fail-loud verdict --
$manual = [ordered]@{
  live_x_top    = @{ PRB = 841;  PRC = 839 }
  full_tree_v   = @{ PRB = 1402; PRC = $null }
  attn_sandbox  = @{ PRB = 363;  PRC = $null }
  upabl_top     = @{ PRB = 226;  PRC = 226 }
  order_lines   = @{ PRB = 572;  PRC = 572 }
  commit_face   = @{ PRB = 609;  PRC = 609 }
}
if ($TamperTest) { $manual.live_x_top.PRB = 500 }   # negative injection: 340/841=40% >> 5%, must trigger exit code 2

function Test-Recon {
  param([string]$Key, [int]$Actual)
  $prb = $manual[$Key].PRB; $prc = $manual[$Key].PRC
  $row = [ordered]@{ actual = $Actual }
  foreach ($seat in @('PRB','PRC')) {
    $m = $manual[$Key].$seat
    if ($null -eq $m) { $row[$seat] = $null; continue }
    $d = [math]::Round((($Actual - $m) / $m) * 100, 2)
    $row[$seat] = @{ manual = $m; delta_pct = $d; verdict = $(if ([math]::Abs($d) -gt 5) { 'FAIL(>5%)' } else { 'PASS' }) }
    if ([math]::Abs($d) -gt 5) { $script:FailLoud = $true }
  }
  $row
}

$recon = [ordered]@{}
if ($null -ne $liveTop)      { $recon['live_x_top']    = Test-Recon 'live_x_top'    $liveTop }
if ($null -ne $fullTree)     { $recon['full_tree_v']   = Test-Recon 'full_tree_v'   $fullTree }
if ($null -ne $attnSandbox)  { $recon['attn_sandbox']  = Test-Recon 'attn_sandbox'  $attnSandbox }
if ($null -ne $upablTop)     { $recon['upabl_top']     = Test-Recon 'upabl_top'     $upablTop }
if ($null -ne $orderMax)     { $recon['order_lines']   = Test-Recon 'order_lines'   $orderMax }
if ($null -ne $faceLiveDir)  { $recon['commit_face']   = Test-Recon 'commit_face'   $faceLiveDir }

# --- JSON assembly ---------------------------------------------------------------
$stats = [ordered]@{
  schema       = 'cw.tree-stats/v1 (S7/PA4+PB6)'
  generated_at = (Get-Date -Format 'yyyy-MM-dd HH:mm:ss zzz')
  head_note    = $headNote
  paper_citation_caliber = @{
    fixed    = 'side_tree_top_level'
    statement= '论文引用口径固定=侧树顶层(Live_X 深度0 *.v, 沙箱系子目录天然排除); 本期实测=' + $liveTop + '; 口径定义防锈, 数值随树面时点漂移属正常(PB6)'
  }
  calibers     = [ordered]@{
    A_registration = [ordered]@{ order_lines = $orderLines; order_lines_max = $orderMax; order_consistency = $orderConsist; commit_face_live_dir = $faceLiveDir; commit_face_repo_all_v = $faceRepoAll }
    B_side_tree_top= [ordered]@{ live_x_top = $liveTop; upabl_top = $upablTop }
    C_sandbox      = [ordered]@{ attn_sandbox = $attnSandbox }
  }
  dimensions   = [ordered]@{
    full_tree_v   = $fullTree
    live_x_top    = $liveTop
    upabl_top     = $upablTop
    upabl_recursive = $upablRec
    attn_sandbox  = $attnSandbox
    order_lines   = $orderMax
    commit_face   = $faceLiveDir
  }
  decomposition_sanity = [ordered]@{
    formula = 'full_tree_v = live_x_top + subdir_v; subdir_v = attn_sandbox + expired_archive + experiment_dirs + ...'
    note    = '沙箱 363 为 09-22 双席手测同值锚——口径定义经锚定复核'
  }
  reconciliation = $recon
  fail_loud    = [ordered]@{
    rule = '|actual-manual|/manual > 5% => exit 2, 并列存证禁硬判'
    triggered = $script:FailLoud
  }
}
$json = $stats | ConvertTo-Json -Depth 8

if (-not $SelfTest) {
  if ([string]::IsNullOrEmpty($OutFile)) { $OutFile = Join-Path $PSScriptRoot 'tree-stats.json' }
  [System.IO.File]::WriteAllText($OutFile, $json, (New-Object System.Text.UTF8Encoding($false)))
  Write-Host "tree-stats.json => $OutFile"
} else {
  # Self-test mode: reconciliation table printed to screen, JSON written as usual (for pasting into reports)
  if ([string]::IsNullOrEmpty($OutFile)) { $OutFile = Join-Path $PSScriptRoot 'tree-stats.json' }
  [System.IO.File]::WriteAllText($OutFile, $json, (New-Object System.Text.UTF8Encoding($false)))
  Write-Host '=== S7 六维×三口径 自测对账表 (实测 vs PR-B/PR-C 09-22 手测) ==='
  Write-Host ('{0,-14}{1,8} | {2:>6}/{3,-10} | {4:>6}/{5,-10} | {6}' -f 'dimension','actual','PRB','d%','PRC','d%','verdict')
  foreach ($k in $recon.Keys) {
    $r = $recon[$k]; $b = $r['PRB']; $c = $r['PRC']
    $bs = if ($b) { '{0} {1,6}%' -f $b.manual, $b.delta_pct } else { '  --' }
    $cs = if ($c) { '{0} {1,6}%' -f $c.manual, $c.delta_pct } else { '  --' }
    $allv = @(); if ($b) { $allv += $b.verdict }; if ($c) { $allv += $c.verdict }
    $v = if ($allv -contains 'FAIL(>5%)') { 'FAIL>5% 并列存证·禁硬判' } else { 'PASS(<5%)' }
    Write-Host ('{0,-14}{1,8} | {2,-16} | {3,-16} | {4}' -f $k, $r.actual, $bs, $cs, $v)
  }
  Write-Host ('order 三方一致性: {0}  |  HEAD: {1}' -f $orderConsist, $headNote)
}

if ($TamperTest) {
  if ($script:FailLoud) { Write-Host 'TamperTest: fail-loud 正确触发(退出码2预期)'; exit 2 }
  else { Write-Host 'TamperTest: 负向注入未被捕获 = 工具失效!'; exit 3 }
}
# fail-loud gate: local default exit code 2 (co-exist evidence, no forced judgment); the -CI face (record-only) does not raise the screen, the verdict is persisted with the JSON for audit.
if ($script:FailLoud -and -not $CI) { exit 2 }
exit 0
