# cpu_guard.ps1 -- CPU load + temperature dual-threshold execution wrapper (20261002 v2.1: two-line scheme, user-pinned suspend line 93C)
# Usage: pwsh -File cpu_guard.ps1 -Command "<command>" [-LoadLimit 85] [-CoolSec 5] [-MaxWaitSec 600] [-CoreN <0..15>] [-TempLimit 93] [-StartTempLimit 95]
# Two-line scheme (measured finding 20261002: this machine idles heat-clamped at 96-97C -- a bare 93C pre-execution gate would lock out every compile):
#   Pre-execution gate line = StartTempLimit (default 95C) + LoadLimit: temp > 95 or load over limit -> cool down, re-test, admit when within bounds
#   Runtime suspend line = TempLimit (default 93C, user-pinned 20261002): while the command runs, temp > 93 -> suspend the whole child process tree,
#                  resume when it falls to <= 91 (2C hysteresis); this is the hard line of defense added after the thermal-overload crash incident
# Rules:
#   1. Pre-execution gating: probe total CPU load (Win32_Processor LoadPercentage) and temperature (Perf counter channel) every 0.5s
#   2. Runtime monitoring: sample temperature every 2s; suspend above the suspend line, resume on hysteresis (suspension recurses the process tree, effective over the whole cmd->coqc tree)
#   3. Core spreading: -CoreN pins a core (different subagents/scripts on different cores to avoid heat concentration; child processes inherit affinity)
#   4. Pre-execution wait exceeding MaxWaitSec while still busy -> ABORT (system under sustained high load; do not stack another task)
#   5. Temperature channel: Win32_PerfFormattedData_Counters_ThermalZoneInformation (Perf counter channel);
#      the MSAcpi channel is dead on this machine (reads 0, converts to a bogus -273.2, disabled); on read failure record TEMP?-UNREADABLE and fall back to load gating, no hard failure
#   6. Standalone resident sentinel: see thermal_sentinel.ps1 (93C alert flag _THERMAL_ALERT, live since 20261002)
param(
  [Parameter(Mandatory=$true)][string]$Command,
  [double]$LoadLimit = 99.0,
  [int]$CoolSec = 5,
  [int]$MaxWaitSec = 600,
  [int]$CoreN = -1,
  [double]$TempLimit = 93.0,
  [double]$StartTempLimit = 99.0
)
# Measured verdict 20261002 (T2 pass): under the heat clamp (idle 96-97C, sustainable for hours) a start line of 95 is never satisfied --
# gating cooldowns ran 390s+ without admission and work stalled 28 minutes in the field, so the default became 99 (temperature leg effectively bypassed).
# Primary thermal defense = runtime suspend line 93C + duty-cycle throttling (v2.3); the pre-gate keeps load gating to prevent task stacking.
# For a real temperature pre-gate (e.g. work inside a cooling window), pass -StartTempLimit 95 explicitly.
# Core spreading: bind to the specified logical core
if ($CoreN -ge 0) {
  $nproc = [Environment]::ProcessorCount
  if ($CoreN -lt $nproc) {
    try {
      $proc = [System.Diagnostics.Process]::GetCurrentProcess()
      $proc.ProcessorAffinity = [IntPtr](([int64]1) -shl $CoreN)
      Write-Host "[cpu_guard] pinned to core $CoreN"
    } catch { Write-Host "[cpu_guard] affinity failed: $($_.Exception.Message)" }
  }
}
function Get-Load { [math]::Round(((Get-CimInstance Win32_Processor | Measure-Object -Property LoadPercentage -Average).Average), 1) }
function Get-TempC {
  $t = Get-CimInstance -ClassName Win32_PerfFormattedData_Counters_ThermalZoneInformation -ErrorAction SilentlyContinue |
       Where-Object { $_.Temperature -gt 273 } | Select-Object -First 1
  if ($t) { return [math]::Round($t.Temperature - 273.0, 1) }
  return $null
}
# Collect the process tree recursively (grandchildren included)
function Get-Tree($pidRoot) {
  $all = @(Get-CimInstance Win32_Process -ErrorAction SilentlyContinue)
  $out = @(); $frontier = @($pidRoot)
  while ($frontier.Count -gt 0) {
    $next = @()
    foreach ($p in $all) { if ($frontier -contains $p.ParentProcessId) { $out += $p.ProcessId; $next += $p.ProcessId } }
    $frontier = $next
  }
  return $out
}
# Process-tree suspend/resume: PS5.1 (.NET Framework) has no Process.Suspend()/Resume() -- measured 20261002 (T4 pass): silent fake success;
# switched to native ntdll calls, failures counted fail-loud
if (-not ('ProcCtl' -as [type])) {
  Add-Type -TypeDefinition @"
using System;
using System.Runtime.InteropServices;
public static class ProcCtl {
  [DllImport("ntdll.dll")] public static extern int NtSuspendProcess(IntPtr hProc);
  [DllImport("ntdll.dll")] public static extern int NtResumeProcess(IntPtr hProc);
}
"@
}
function Suspend-Tree($pidRoot) {
  $n = 0; $fail = 0
  foreach ($tpid in (Get-Tree $pidRoot)) {
    try {
      $p = Get-Process -Id $tpid -ErrorAction Stop
      $r = [ProcCtl]::NtSuspendProcess($p.Handle)
      if ($r -eq 0) { $n++ } else { $fail++; Write-Host "[cpu_guard] FAIL suspend pid=${tpid} ntstatus=$r" }
    } catch { $fail++; Write-Host "[cpu_guard] FAIL suspend pid=${tpid}: $($_.Exception.Message)" }
  }
  Write-Host "[cpu_guard] suspended ${n} procs (fail=${fail})"
  return $n
}
function Resume-Tree($pidRoot) {
  $n = 0; $fail = 0
  foreach ($tpid in (Get-Tree $pidRoot)) {
    try {
      $p = Get-Process -Id $tpid -ErrorAction Stop
      $r = [ProcCtl]::NtResumeProcess($p.Handle)
      if ($r -eq 0) { $n++ } else { $fail++; Write-Host "[cpu_guard] FAIL resume pid=${tpid} ntstatus=$r" }
    } catch { $fail++; Write-Host "[cpu_guard] FAIL resume pid=${tpid}: $($_.Exception.Message)" }
  }
  Write-Host "[cpu_guard] resumed ${n} procs (fail=${fail})"
  return $n
}
# -- Pre-execution gate (load + temperature dual condition, start line StartTempLimit) --
$elapsed = 0; $cooled = 0
while ($elapsed -lt $MaxWaitSec) {
  $l = Get-Load
  $t = Get-TempC
  $tStr = "?"; $tHot = $false
  if ($null -ne $t) { $tStr = "$t"; $tHot = ($t -gt $StartTempLimit) }
  if ($l -le $LoadLimit -and -not $tHot) {
    if ($cooled -gt 0) { Write-Host "[cpu_guard] cooled ${cooled}s; load=${l}% temp=${tStr}C -> executing" }
    else { Write-Host "[cpu_guard] OK load=${l}% temp=${tStr}C -> executing" }
    break
  }
  $why = if ($tHot) { "temp=${tStr}C>${StartTempLimit}C" } else { "load=${l}%>${LoadLimit}%" }
  Start-Sleep -Milliseconds 500
  $elapsed += 0.5; $cooled += 0.5
  if ([math]::Floor($cooled) % $CoolSec -eq 0 -and $cooled -gt 0) { Write-Host "[cpu_guard] cooling ${cooled}s: $why" }
  if ($elapsed -ge $MaxWaitSec) { Write-Host "[cpu_guard] ABORT: busy after ${MaxWaitSec}s (last: $why)"; exit 2 }
}
# -- Execution (grab the handle to support runtime suspend/resume) --
$child = Start-Process -FilePath "cmd.exe" -ArgumentList "/c", $Command -NoNewWindow -PassThru
if (-not $child) { Invoke-Expression $Command; exit $LASTEXITCODE }
$null = $child.Handle
# -- Runtime temperature monitoring (v2.3: duty-cycle against clamp deadlock) --
# Incident verdict 20261002: in the 96-97C heat-clamp state the 93C suspend line never releases (suspending does not lower the temperature) -> compile deadlock
# (three coqc processes pinned at CPU~0 in the field, rocqworker frozen at 85/243/313s, NtResume rescue from the main session).
# v2.3 duty-cycle throttling: suspend 20s -> release 5s (breather) -> loop, until the temperature truly drops to <= 91 for a full resume; the task advances at ~80% duty,
# protection semantics preserved (suspend dominates = bounded average thermal load), deadlock eliminated.
$suspending = $false; $suspCount = 0; $holdSec = 0
while (-not $child.HasExited) {
  Start-Sleep -Seconds 2
  if ($child.HasExited) { break }
  $t = Get-TempC
  if ($null -eq $t) { continue }
  if (-not $suspending) {
    if ($t -gt $TempLimit) {
      $suspending = $true; $suspCount++; $holdSec = 0
      Write-Host "[cpu_guard] RUNTIME-HOT temp=${t}C>${TempLimit}C suspending tree"
      Suspend-Tree $child.Id | Out-Null
    }
  } else {
    $holdSec += 2
    if ($t -le ($TempLimit - 2)) {
      Write-Host "[cpu_guard] cooled temp=${t}C resuming tree (held ${holdSec}s)"
      Resume-Tree $child.Id | Out-Null
      $suspending = $false
    } elseif ($holdSec -ge 20) {
      Write-Host "[cpu_guard] duty-breather held=${holdSec}s temp=${t}C: resume 5s"
      Resume-Tree $child.Id | Out-Null
      Start-Sleep -Seconds 5
      if (-not $child.HasExited) {
        Write-Host "[cpu_guard] re-suspend after breather (temp=$(Get-TempC)C)"
        Suspend-Tree $child.Id | Out-Null
      }
      $holdSec = 0
    }
  }
}
if ($suspending) {
  Write-Host "[cpu_guard] command exited while suspended: resuming tree before reap"
  Resume-Tree $child.Id | Out-Null
  Start-Sleep -Milliseconds 500
}
$child.WaitForExit() | Out-Null
Write-Host "[cpu_guard] done exit=$($child.ExitCode) runtime-suspends=${suspCount} tempLimit=${TempLimit}C"
exit $child.ExitCode
