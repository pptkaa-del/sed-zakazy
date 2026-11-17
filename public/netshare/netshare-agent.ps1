<#
  Агент «Сетевая папка» для программы «Управление предприятием» (Windows, без установки Node.js).
  Слушает только 127.0.0.1 и отдаёт список файлов и папок (только чтение).
  Программа обращается к нему через обратный SSH-туннель (OpenSSH есть в Windows 10 / Server 2019 и новее):
    ssh -N -R 127.0.0.1:<порт на сервере программы>:127.0.0.1:<порт агента> <пользователь>@<сервер программы>
  Запуск:
    powershell -ExecutionPolicy Bypass -File netshare-agent.ps1 -Token <ключ из программы> [-Port 8765] [-Allow "D:\,E:\"]
#>
param([Parameter(Mandatory = $true)][string]$Token, [int]$Port = 8765, [string]$Allow = '')
$ErrorActionPreference = 'Stop'
if ($Token.Length -lt 16) { Write-Error 'Укажите ключ из программы: -Token <ключ>'; exit 1 }
$allowList = @($Allow -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ } | ForEach-Object { [System.IO.Path]::GetFullPath($_) })
function Test-Inside([string]$child, [string]$root) {
  $c = [System.IO.Path]::GetFullPath($child).TrimEnd('\'); $r = [System.IO.Path]::GetFullPath($root).TrimEnd('\')
  return ($c -ieq $r) -or $c.StartsWith($r + '\', [System.StringComparison]::OrdinalIgnoreCase)
}
function Send-Json($stream, [int]$code, $obj) {
  $body = [System.Text.Encoding]::UTF8.GetBytes((ConvertTo-Json -InputObject $obj -Depth 5 -Compress))
  $status = @{ 200 = 'OK'; 400 = 'Bad Request'; 403 = 'Forbidden'; 404 = 'Not Found'; 405 = 'Method Not Allowed'; 500 = 'Internal Server Error' }[$code]
  $head = [System.Text.Encoding]::ASCII.GetBytes("HTTP/1.1 $code $status`r`nContent-Type: application/json; charset=utf-8`r`nContent-Length: $($body.Length)`r`nConnection: close`r`n`r`n")
  $stream.Write($head, 0, $head.Length); $stream.Write($body, 0, $body.Length); $stream.Flush()
}
$listener = New-Object System.Net.Sockets.TcpListener([System.Net.IPAddress]::Loopback, $Port)
$listener.Start()
Write-Host "Агент «Сетевая папка» слушает 127.0.0.1:$Port"
while ($true) {
  $client = $listener.AcceptTcpClient()
  try {
    $client.ReceiveTimeout = 10000; $stream = $client.GetStream()
    $reader = New-Object System.IO.StreamReader($stream, [System.Text.Encoding]::ASCII, $false, 8192, $true)
    $first = $reader.ReadLine(); $headers = @{}
    while (($line = $reader.ReadLine()) -ne $null -and $line -ne '') { $i = $line.IndexOf(':'); if ($i -gt 0) { $headers[$line.Substring(0, $i).Trim().ToLower()] = $line.Substring($i + 1).Trim() } }
    $parts = "$first" -split ' '
    if ($parts[0] -ne 'GET') { Send-Json $stream 405 @{ ok = $false; error = 'Только чтение' }; continue }
    if ($headers['x-token'] -cne $Token) { Send-Json $stream 403 @{ ok = $false; error = 'Неверный ключ агента' }; continue }
    $target = $parts[1]; $qi = $target.IndexOf('?'); $pathPart = if ($qi -ge 0) { $target.Substring(0, $qi) } else { $target }
    $q = @{}; if ($qi -ge 0) { foreach ($kv in $target.Substring($qi + 1) -split '&') { $p = $kv -split '=', 2; if ($p.Count -eq 2) { $q[$p[0]] = [System.Uri]::UnescapeDataString($p[1].Replace('+', ' ')) } } }
    if ($pathPart -eq '/ping') { Send-Json $stream 200 @{ ok = $true; agent = 'sed-netshare'; v = 1; platform = 'win32'; host = $env:COMPUTERNAME }; continue }
    if ($pathPart -ne '/list') { Send-Json $stream 404 @{ ok = $false; error = 'Не найдено' }; continue }
    $root = "$($q['root'])"; $sub = "$($q['path'])"
    if (-not $root) { Send-Json $stream 400 @{ ok = $false; error = 'Не указан диск или папка' }; continue }
    if ($allowList.Count -gt 0 -and -not ($allowList | Where-Object { Test-Inside $root $_ })) { Send-Json $stream 403 @{ ok = $false; error = 'Этот диск или папка не разрешены агенту (-Allow)' }; continue }
    if (($sub -split '[\\/]') -contains '..') { Send-Json $stream 400 @{ ok = $false; error = 'Недопустимый путь' }; continue }
    $full = [System.IO.Path]::GetFullPath([System.IO.Path]::Combine($root, $sub))
    if (-not (Test-Inside $full $root)) { Send-Json $stream 400 @{ ok = $false; error = 'Недопустимый путь' }; continue }
    if (-not [System.IO.Directory]::Exists($full)) { Send-Json $stream 404 @{ ok = $false; error = 'Папка не найдена' }; continue }
    try {
      $items = @([System.IO.DirectoryInfo]::new($full).GetFileSystemInfos() | Select-Object -First 5000)
      $entries = @($items | ForEach-Object { $d = ($_.Attributes -band [System.IO.FileAttributes]::Directory) -ne 0
        @{ name = $_.Name; dir = $d; size = $(if ($d) { $null } else { $_.Length }); mtime = $_.LastWriteTimeUtc.ToString('o') } })
      Send-Json $stream 200 @{ ok = $true; path = $sub; total = $items.Count; entries = $entries }
    } catch [System.UnauthorizedAccessException] { Send-Json $stream 403 @{ ok = $false; error = 'Нет доступа к папке' } }
  } catch { try { Send-Json $stream 500 @{ ok = $false; error = "$($_.Exception.Message)" } } catch {} }
  finally { $client.Close() }
}
