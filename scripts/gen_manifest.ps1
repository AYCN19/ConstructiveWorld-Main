<#
=====================================================================
 gen_manifest.ps1 -- S7/PA2 (tool half) snapshot manifest generator
 (ConstructiveWorld reinforcement SLICE-S7, tool family, zero compile / zero network / zero git write)
---------------------------------------------------------------------
 Function: compute SHA1 + size for every file on the snapshot export face, and record a commit note in the header
       (main repo HEAD sha+date+subject at export time, obtained read-only via git) -> snapshot-manifest.json
 Schedule: the real export belongs after R112 -- the original work-order plan; a read-only git measurement on 09-22 (this pass) showed R112/R113 already landed in the cloud
       (HEAD=1719a2d), so the real-export window is open, but apply/real runs belong to the R11x registration wave / registration pass; this item delivers the tool + self-test only.
 Usage:
   pwsh -File gen_manifest.ps1 -SelfTest                    # known-answer self-test (acceptance mode)
   pwsh -File gen_manifest.ps1 [-SnapshotDir <snapshot face>] [-OutFile <json>]
 Territory: read-only traversal + the only write surface = -OutFile (default snapshot-manifest.json beside this tool)
       and the -SelfTest temp directory (_selftest_manifest\ beside this tool, cleaned when the run ends).
=====================================================================
#>
[CmdletBinding()]
param(
  [string]$SnapshotDir = 'D:\ComplexAnalysis\ConstructiveWorld_Live',
  [string]$MainRepo    = 'D:\ComplexAnalysis\ConstructiveWorld-Main',
  [string]$OutFile     = '',
  [string]$Commit      = '',     # when given explicitly, overrides auto-detection (for export-script annotation)
  [switch]$SelfTest
)
$ErrorActionPreference = 'Stop'

function New-Manifest {
  param([string]$Dir, [string]$CommitNote)
  if (-not (Test-Path -LiteralPath $Dir)) { throw "SnapshotDir 不存在: $Dir" }
  $files = @(Get-ChildItem -LiteralPath $Dir -Recurse -File | Sort-Object FullName)
  $entries = foreach ($f in $files) {
    [ordered]@{
      path = [System.IO.Path]::GetFullPath($f.FullName).Substring(
               [System.IO.Path]::GetFullPath($Dir).TrimEnd('\','/').Length + 1).Replace('\','/')
      bytes = $f.Length
      sha1  = (Get-FileHash -LiteralPath $f.FullName -Algorithm SHA1).Hash.ToLowerInvariant()
    }
  }
  [ordered]@{
    schema        = 'cw.snapshot-manifest/v1 (S7/PA2 工具半件)'
    generated_at  = (Get-Date -Format 'yyyy-MM-dd HH:mm:ss zzz')
    snapshot_dir  = (Resolve-Path -LiteralPath $Dir).Path
    commit_note   = $CommitNote      # overall note beyond the per-file entries: main repo HEAD at export time (or explicit -Commit)
    commit_scope  = 'HEAD-at-generation-time (主库导出时点注记, 非逐文件 blob 声明)'
    file_count    = $entries.Count
    total_bytes   = ($entries | Measure-Object -Property bytes -Sum).Sum
    files         = $entries
  }
}

function Get-HeadNote {
  param([string]$Repo, [string]$Explicit)
  if (-not [string]::IsNullOrWhiteSpace($Explicit)) { return $Explicit }
  try {
    $h = & git -C $Repo log -1 --format='%H|%ad|%s' --date=iso 2>$null
    if ($LASTEXITCODE -eq 0 -and $h) { return ($h -join '') }
  } catch { }
  return 'commit-unavailable(git 缺席/非仓: 注记位留空, fail-loud 不沉默)'
}

if ($SelfTest) {
  # ---- Known-answer two-way self-test: SHA1 standard vectors + structure assertions + determinism assertion + note assertion ----
  $here = if ($PSScriptRoot) { $PSScriptRoot } else { (Get-Location).Path }
  $tmp  = Join-Path $here '_selftest_manifest'
  if (Test-Path -LiteralPath $tmp) { Remove-Item -LiteralPath $tmp -Recurse -Force }
  New-Item -ItemType Directory -Path (Join-Path $tmp 'sub') | Out-Null
  [System.IO.File]::WriteAllText((Join-Path $tmp 'abc.txt'),  'abc')                       # → a9993e36...
  [System.IO.File]::WriteAllText((Join-Path $tmp 'empty.txt'), '')                         # → da39a3ee...
  [System.IO.File]::WriteAllText((Join-Path $tmp 'sub\nested.v'), 'Require Import Nothing. (* S7 known-answer *)')
  $nestedSha = (Get-FileHash -LiteralPath (Join-Path $tmp 'sub\nested.v') -Algorithm SHA1).Hash.ToLowerInvariant()

  $m1 = New-Manifest -Dir $tmp -CommitNote 'SELFTEST-COMMIT-ANNOTATION|2026-09-22|S7 known-answer'
  $j1 = $m1 | ConvertTo-Json -Depth 6
  $m2 = New-Manifest -Dir $tmp -CommitNote 'SELFTEST-COMMIT-ANNOTATION|2026-09-22|S7 known-answer'
  $j2 = $m2 | ConvertTo-Json -Depth 6

  $fails = @()
  if ($m1.file_count -ne 3)                                              { $fails += "count=$($m1.file_count)≠3" }
  $byPath = @{}; foreach ($e in $m1.files) { $byPath[$e.path] = $e }
  if ($byPath['abc.txt'].sha1   -ne 'a9993e364706816aba3e25717850c26c9cd0d89d') { $fails += 'SHA1(abc) 向量不符' }
  if ($byPath['empty.txt'].sha1 -ne 'da39a3ee5e6b4b0d3255bfef95601890afd80709') { $fails += 'SHA1(empty) 向量不符' }
  if ($byPath['sub/nested.v'].sha1 -ne $nestedSha)                       { $fails += 'SHA1(nested) 自洽不符' }
  if ($byPath['sub/nested.v'].bytes -ne (Get-Item (Join-Path $tmp 'sub\nested.v')).Length) { $fails += 'bytes 字段不符' }
  if ($j1 -ne $j2)                                                       { $fails += '两次生成不字节一致(非确定性!)' }
  if ($m1.commit_note -notlike 'SELFTEST-COMMIT-ANNOTATION*')            { $fails += 'commit 注记丢失' }
  if ($fails) { $fails | ForEach-Object { Write-Host "SELFTEST FAIL: $_" }; Remove-Item -LiteralPath $tmp -Recurse -Force; exit 3 }

  Remove-Item -LiteralPath $tmp -Recurse -Force
  Write-Host '=== gen_manifest 自测: 5/5 断言 PASS ==='
  Write-Host '  [1] file_count=3 (递归含子目录)            PASS'
  Write-Host '  [2] SHA1("abc")=a9993e36… 标准向量           PASS'
  Write-Host '  [3] SHA1("")=da39a3ee… 空文件向量            PASS'
  Write-Host '  [4] 两轮生成字节级一致(确定性)               PASS'
  Write-Host '  [5] commit 注记字段在位                      PASS'
  Write-Host '  (负向面: 缺目录即 throw, 见领地注记 —— fail-loud 不沉默)'
  Write-Host 'SelfTest 临时目录已清理。实导出(-SnapshotDir 真面)归 R11x 注册波执行。'
  exit 0
}

if ([string]::IsNullOrEmpty($OutFile)) { $OutFile = Join-Path $PSScriptRoot 'snapshot-manifest.json' }
$manifest = New-Manifest -Dir $SnapshotDir -CommitNote (Get-HeadNote -Repo $MainRepo -Explicit $Commit)
[System.IO.File]::WriteAllText($OutFile, ($manifest | ConvertTo-Json -Depth 6), (New-Object System.Text.UTF8Encoding($false)))
Write-Host ("snapshot-manifest.json => {0}  (files={1}, commit_note={2})" -f $OutFile, $manifest.file_count, $manifest.commit_note)
exit 0
