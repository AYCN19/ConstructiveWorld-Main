# thermal_sentinel.ps1 -- temperature monitoring sentinel (rebuilt 20261001, user-pinned limit 93C)
# Usage: powershell -File thermal_sentinel.ps1 [-TempLimit 93] [-IntervalSec 10] [-LogFile <csv>]
# Behavior:
#   1. Read the Perf counter channel temperature every IntervalSec (Win32_PerfFormattedData_Counters_ThermalZoneInformation)
#      -- the MSAcpi channel is dead on this machine (reads 0, converts to a bogus -273.2, disabled)
#   2. Append to _THERMAL_log.csv (time, tempC[,ALERT])
#   3. Temp > TempLimit -> write the _THERMAL_ALERT flag (time + top-3 load processes); auto-clear once it falls back to <= TempLimit-2
#   4. Count consecutive read failures and log failed rows as ERR without fabricating values; exit when the _THERMAL_SENTINEL_STOP flag exists
param(
  [double]$TempLimit = 93.0,
  [int]$IntervalSec = 10,
  [string]$LogFile = "D:\ComplexAnalysis\新算法实践\attn\_THERMAL_log.csv",
  [string]$AlertFlag = "D:\ComplexAnalysis\新算法实践\attn\_THERMAL_ALERT",
  [string]$StopFlag = "D:\ComplexAnalysis\新算法实践\attn\_THERMAL_SENTINEL_STOP"
)
function Get-TempC {
  $t = Get-CimInstance -ClassName Win32_PerfFormattedData_Counters_ThermalZoneInformation -ErrorAction SilentlyContinue |
       Where-Object { $_.Temperature -gt 273 } | Select-Object -First 1
  if ($t) { return [math]::Round($t.Temperature - 273.0, 1) }
  return $null
}
$failStreak = 0
$alerting = $false
Write-Host "[thermal_sentinel] started limit=${TempLimit}C interval=${IntervalSec}s log=$LogFile"
while ($true) {
  if (Test-Path $StopFlag) { Write-Host "[thermal_sentinel] stop flag seen, exiting"; exit 0 }
  $ts = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
  $c = Get-TempC
  if ($null -eq $c) {
    $failStreak++
    if ($failStreak -ge 3) { Add-Content -Path $LogFile -Value "$ts,ERR" }
  } else {
    $failStreak = 0
    if ($c -gt $TempLimit) {
      Add-Content -Path $LogFile -Value "$ts,$c,ALERT"
      if (-not $alerting) {
        $alerting = $true
        $top = Get-Process | Sort-Object CPU -Descending | Select-Object -First 3 |
               ForEach-Object { "$($_.Id):$($_.ProcessName)" }
        Set-Content -Path $AlertFlag -Value "$ts TEMP=$c LIMIT=$TempLimit top=$($top -join ' ')"
        Write-Host "[thermal_sentinel] ALERT ${c}C > ${TempLimit}C flag written"
      }
    } else {
      Add-Content -Path $LogFile -Value "$ts,$c"
      if ($alerting -and $c -le ($TempLimit - 2)) {
        $alerting = $false
        Remove-Item $AlertFlag -ErrorAction SilentlyContinue
        Write-Host "[thermal_sentinel] recovered ${c}C, alert cleared"
      }
    }
  }
  Start-Sleep -Seconds $IntervalSec
}
