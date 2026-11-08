# cpu_guard.ps1 — CPU 负载 + 温度双维调控执行包装（20261005 v3：热等级档位制——比例式节流·治 bang-bang 振荡）
# v3 增补（20261005 用户令 GO）：读等级文件 _THERMAL_LEVEL（G0-G3·哨兵 v2 写入）→ 档位化占空（G1 放7/挂3·G2 放3/挂7）
#   ＋G≥2 子进程树降优先级 BelowNormal＋G3 保留 v2.3 硬挂起线与喘息；CLI 完全向后兼容（等级文件缺省=G0=原行为）。
# 用法: pwsh -File cpu_guard.ps1 -Command "<命令>" [-LoadLimit 85] [-CoolSec 5] [-MaxWaitSec 600] [-CoreN <0..15>] [-TempLimit 93] [-StartTempLimit 95]
# 双线制（20261002 实测定谳：本机 idle 积热常态即 96-97C 钳位——执行前门控裸用 93 会锁死一切编译）：
#   执行前门控线 = StartTempLimit(默认 95C) + LoadLimit：温度>95 或 负载超限 → 冷却后重测，达标放行
#   执行中挂起线 = TempLimit(默认 93C，用户 20261002 钉值)：命令运行中温度>93 → 挂起子进程树整树，
#                  降至 <=91(迟滞2C) → 恢复；这是热过载宕机事故后的硬防线
# 规则：
#   1. 执行前门控：每 0.5s 探测 CPU 总负载(Win32_Processor LoadPercentage)与温度(Perf 通道)
#   2. 执行中监控：每 2s 采样温度，超挂起线挂起/迟滞恢复（挂起经进程树递归，cmd→coqc 整树生效）
#   3. 核心分散：-CoreN 绑核（不同子代理/脚本不同核，避免热集中；子进程继承亲和性）
#   4. 执行前等待超 MaxWaitSec 仍忙 → ABORT（系统持续高负载，不叠加任务）
#   5. 温度通道：Win32_PerfFormattedData_Counters_ThermalZoneInformation（Perf 通道）；
#      MSAcpi 通道本机已死(读 0 换算 -273.2 假值,禁用)；读失败记 TEMP?-UNREADABLE 按负载兜底不硬失败
#   6. 独立常驻哨兵见 thermal_sentinel.ps1（93C 告警旗标 _THERMAL_ALERT，20261002 已上线）
param(
  [Parameter(Mandatory=$true)][string]$Command,
  [double]$LoadLimit = 99.0,
  [int]$CoolSec = 5,
  [int]$MaxWaitSec = 600,
  [int]$CoreN = -1,
  [double]$TempLimit = 93.0,
  [double]$StartTempLimit = 99.0,
  [int]$GearForce = -1,
  [string]$LevelFile = 'D:\ComplexAnalysis\新算法实践\attn\_THERMAL_LEVEL',
  [int]$StaleGear = 3,
  [double]$StaleSec = 120,
  [switch]$AllowG3,
  [string]$CrisisFile = 'D:\ComplexAnalysis\新算法实践\attn\_THERMAL_CRISIS'
)
# ── v4（20261010 用户令·P0/P1/P2 整批立法）──
#   闸一 鲜度闸：等级文件 mtime 陈旧 >StaleSec(120s) 或缺失/不可解析 → 按保守档 StaleGear(默认G3) 执行＋响亮落日志
#        （哨兵死/rogue 写手/文件误删三种盲窗一并封堵；前闸与运行时共用 Get-GearState）；
#   闸二 G3 发射闸：「G3 编译 HOLD」自 v4 起为机械闸——档位≥3 或 _THERMAL_CRISIS 危机旗在挂 → 前闸直接拒绝
#        发射（exit 3·不进冷却等待）；唯 -AllowG3 显式授权可越（越权留痕于输出）。GearForce 不构成越权凭证；
#   补一 传感失效 duty-only：运行中读温连续 null ≥3 轮（6s）转 duty-only 模式（档位占空不依赖温度·HARD 线
#        暂失效并响亮落日志，读数恢复即重装填）——治「传感死＝零节流盲跑」；
#   补二 DUTY→HARD 升级：占空挂起期间温度冲破 TempLimit 即升级 HARD 线（原实现只等占空期满）。
#   退出码：0=命令正常｜2=前闸忙等超时 ABORT｜3=G3-HOLD 拒绝发射。
# 20261002 T2 席实测定谳：启动线 95 在钳位态（idle 96-97C，可持续数小时）下永不满足——
# 守门 cooling 390s+ 不放行、件停摆 28 分钟实锤，故默认值改 99（温度位实质旁路）。
# 防热主防线=运行中挂起线 93C+duty-cycle 占空限流（v2.3）；前闸保留负载门控防叠加。
# 若需真温度前闸（如散热窗作业）可显式传 -StartTempLimit 95。
# ── v3 热等级档位制 ──
$GearProfile = @{
  0 = @{ run = 0; suspend = 0;  priority = 'Normal' }
  1 = @{ run = 7; suspend = 3;  priority = 'Normal' }
  2 = @{ run = 3; suspend = 7;  priority = 'BelowNormal' }
  3 = @{ run = 5; suspend = 20; priority = 'BelowNormal' }
}
function Get-GearState {
  # v4 闸一：档位＋鲜度联合读取。陈旧/缺失/不可解析一律退保守档 StaleGear（默认 G3）。
  if (-not (Test-Path $LevelFile)) {
    return @{ gear = $StaleGear; stale = $true; age = -1.0; why = 'no-levelfile' }
  }
  try {
    $age = ((Get-Date) - (Get-Item -Path $LevelFile -ErrorAction Stop).LastWriteTime).TotalSeconds
    $first = (Get-Content -Path $LevelFile -TotalCount 1 -ErrorAction Stop | Select-Object -First 1)
    if ($first -notmatch '(?i)^G?\s*([0-3])\b') {
      return @{ gear = $StaleGear; stale = $true; age = $age; why = 'unparseable' }
    }
    $g = [int]$Matches[1]
    if ($age -gt $StaleSec) {
      return @{ gear = $StaleGear; stale = $true; age = $age; why = ('stale {0}s' -f [int]$age) }
    }
    return @{ gear = $g; stale = $false; age = $age; why = '' }
  } catch {
    return @{ gear = $StaleGear; stale = $true; age = -1.0; why = 'read-error' }
  }
}
function Get-Gear {
  if ($GearForce -ge 0) { return [Math]::Min(3, [Math]::Max(0, $GearForce)) }
  return (Get-GearState).gear
}
$script:lastPriority = ''
function Apply-Priority($gear, $childId) {
  $want = $GearProfile[$gear].priority
  if ($script:lastPriority -eq $want) { return }
  $n = 0
  foreach ($tpid in (Get-Tree $childId)) {
    try {
      $p = Get-Process -Id $tpid -ErrorAction Stop
      if ([string]$p.PriorityClass -ne $want) { $p.PriorityClass = $want; $n++ }
    } catch { }
  }
  $script:lastPriority = $want
  if ($n -gt 0) { Write-Host "[cpu_guard] gear=$gear priority->$want on $n procs" }
}
# 核心分散：绑定指定逻辑核
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
# 递归收集进程树(含孙代)
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
# 进程树挂起/恢复：PS5.1(.NET Framework)无 Process.Suspend()/Resume()——20261002 T4 实测静默假成功；
# 改 ntdll 原生调用，失败 fail-loud 响亮计数
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
# ── v4 闸二：G3 发射闸（机械 HOLD）──
$gsPre = Get-GearState
$crisisPre = Test-Path $CrisisFile
if (-not $AllowG3 -and ($crisisPre -or $gsPre.gear -ge 3)) {
  $why = if ($crisisPre) { "CRISIS-FLAG $CrisisFile" } else { ("gear=G{0}{1}" -f $gsPre.gear, $(if ($gsPre.stale) { " STALE($($gsPre.why))" } else { '' })) }
  Write-Host "[cpu_guard] G3-HOLD: launch blocked ($why); pass -AllowG3 with explicit authorization"
  exit 3
}
if ($AllowG3) { Write-Host "[cpu_guard] -AllowG3 authorization present: gate bypassed (crisis=$crisisPre pre-gear=$($gsPre.gear) stale=$($gsPre.stale))" }
# ── 执行前门控（负载 + 温度双条件，启动线 StartTempLimit）──
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
# ── 执行（拿句柄以支持执行中挂起/恢复）──
$child = Start-Process -FilePath "cmd.exe" -ArgumentList "/c", $Command -NoNewWindow -PassThru
if (-not $child) { Invoke-Expression $Command; exit $LASTEXITCODE }
$null = $child.Handle
# ── 执行中温度监控（v2.3：duty-cycle 防钳位死锁）──
# 20261002 事故定谳：本机温度钳位态 96-97C 下挂起线 93 永不释放（挂起了温度也不降）→ 编译死锁
# （三 coqc CPU≈0 实锤，rocqworker 85/243/313s 冻结，主会话 NtResume 救援）。
# v2.3 占空限流：挂 20s → 放 5s（breather）→ 循环，直到温度真降 ≤91 彻底恢复；任务以 ~80% 占空推进，
# 防护语义保留（挂起占多数=平均热负载受限），死锁消除。
# ── 执行中监控 v3：热等级档位制 ──
# 硬挂起线 TempLimit(93) 任意档位保持为安全网；G1/G2 追加档位占空（放 run 秒/挂 suspend 秒·2s 粒度）；
# G≥2 子进程树降优先级；每轮 2s 重读等级文件（档位变化即时生效）。
$suspending = $false; $suspCount = 0; $holdSec = 0; $runSec = 0
$suspReason = ''
$lastGear = -1
$nullStreak = 0; $nullMode = $false; $staleLogged = $false
while (-not $child.HasExited) {
  Start-Sleep -Seconds 2
  if ($child.HasExited) { break }
  # v4 闸一（运行时）：档位＋鲜度联合读取；陈旧→保守档＋一次性响亮日志
  $gs = Get-GearState
  $gear = if ($GearForce -ge 0) { [Math]::Min(3, [Math]::Max(0, $GearForce)) } else { $gs.gear }
  if ($gs.stale -and -not $staleLogged) {
    Write-Host "[cpu_guard] LEVELFILE STALE ($($gs.why)): conservative gear G$gear in effect"
    $staleLogged = $true
  } elseif (-not $gs.stale) { $staleLogged = $false }
  if ($gear -ne $lastGear) {
    Write-Host "[cpu_guard] gear=$gear (run=$($GearProfile[$gear].run)s/susp=$($GearProfile[$gear].suspend)s)"
    $lastGear = $gear
  }
  Apply-Priority $gear $child.Id
  $t = Get-TempC
  if ($null -eq $t) {
    # v4 补一：传感失效→duty-only（占空继续·HARD 线失效并响亮落日志，禁零节流盲跑）
    $nullStreak++
    if ($nullStreak -ge 3 -and -not $nullMode) {
      Write-Host "[cpu_guard] TEMP?-UNREADABLE x${nullStreak}: sensor lost -> duty-only mode (HARD line inactive)"
      $nullMode = $true
    }
  } else {
    if ($nullMode) { Write-Host "[cpu_guard] temp restored (${t}C): HARD line re-armed"; $nullMode = $false }
    $nullStreak = 0
  }
  $prof = $GearProfile[$gear]
  if (-not $suspending) {
    if (-not $nullMode -and $null -ne $t -and $t -gt $TempLimit) {
      $suspending = $true; $suspCount++; $holdSec = 0; $suspReason = 'HARD'
      Write-Host "[cpu_guard] RUNTIME-HOT temp=${t}C>${TempLimit}C suspending tree (HARD)"
      Suspend-Tree $child.Id | Out-Null
    } elseif ($prof.run -gt 0) {
      $runSec += 2
      if ($runSec -ge $prof.run) {
        $suspending = $true; $holdSec = 0; $suspReason = 'DUTY'
        Write-Host "[cpu_guard] gear=$gear duty-throttle run=$($runSec)s: suspending $($prof.suspend)s"
        Suspend-Tree $child.Id | Out-Null
      }
    } else { $runSec = 0 }
  } else {
    $holdSec += 2
    # v4 补二：占空挂起期间温度越线→升级 HARD
    if ($suspReason -eq 'DUTY' -and -not $nullMode -and $null -ne $t -and $t -gt $TempLimit) {
      Write-Host "[cpu_guard] temp=${t}C>${TempLimit}C during duty-hold: promoted DUTY->HARD"
      $suspReason = 'HARD'
    }
    if ($suspReason -eq 'HARD' -and -not $nullMode -and $null -ne $t) {
      if ($t -le ($TempLimit - 2)) {
        Write-Host "[cpu_guard] cooled temp=${t}C resuming tree (held ${holdSec}s)"
        Resume-Tree $child.Id | Out-Null
        $suspending = $false; $runSec = 0
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
    } else {
      if ($holdSec -ge $prof.suspend) {
        Write-Host "[cpu_guard] gear=$gear duty-resume after held=$($holdSec)s"
        Resume-Tree $child.Id | Out-Null
        $suspending = $false; $runSec = 0; $holdSec = 0
      }
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
