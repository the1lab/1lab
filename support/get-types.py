#!/usr/bin/env python3
import asyncio
import json
import sys
from typing import List, Dict


async def main() -> None:
  modules: List[str] = [x.strip() for x in sys.stdin]
  sys.stderr.write(f"Getting types for {len(modules)} modules\n")

  result: Dict[str, Dict[str, str]] = {}

  agda_proc = await asyncio.create_subprocess_exec(
    "agda", "--interaction-json", "--local-interfaces",
    stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE
  )
  for module in modules:
    agda_proc.stdin.write(f'IOTCM "_build/all-pages.agda" Interactive Direct (Cmd_show_module_contents_toplevel AsIs "{module}")\n'.encode());
    while True:
      line = (await agda_proc.stdout.readline()).decode()
      if line.startswith("JSON> "):
        line = line[6:]
      data = json.loads(line)
      if "info" in data and "error" in data["info"]:
        sys.stderr.write(f"Error querying {module}:\n")
        sys.stderr.write(data["info"]["error"]["message"])
        break
      elif data['kind'] in ("Status", "RunningInfo", "ClearRunningInfo", "ClearHighlighting", "HighlightingInfo"):
        continue
      elif data["kind"] == "DisplayInfo":
        items: Dict[str, str] = {item['name']: item['term'] for item in data["info"]["contents"]}
        result[module] = items
        break
      else:
        sys.stderr.write(f"Error querying {module}:\n")
        sys.stderr.write(f"Unexpected line {data['kind']}\n")
        sys.exit(1)

  agda_proc.stdin.close()
  if code := await agda_proc.wait() != 0:
    sys.stderr.write(f"Agda exited with {code}")
    sys.exit(1)

  json.dump(result, sys.stdout)


if __name__ == '__main__':
  asyncio.run(main())
