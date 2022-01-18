local cache = {}
local NAME = os.getenv("MODULE_NAME")

if not NAME or NAME == '' then
  error("no NAME specified")
end

local function load_cache()
  local f = io.open("_build/tex_cache" .. NAME .. ".lua", 'r')
  if f == nil then
    return
  end

  local x = load(f:read("*a"))
  if x then
    x(cache)
  end
  f:close()
end

local function trim(s)
  return s:match "^%s*(.-)%s*$"
end

load_cache()

local function add_to_cache(type, key, val)
  cache[type .. '$' .. key] = val
end

local HTML_DIR = os.getenv("HTML_DIR")
local DIAGRAMS = os.getenv("DIAGRAM_LIST")
local makefile = io.open(DIAGRAMS, "w")

return {
  {
    Inlines = function(inlines)
      for i = #inlines-1, 1, -1 do
        local m = inlines[i];
        local t = inlines[i+1];
        if (m.t == 'Math' and t.t == 'Str' and t.text:sub(1,1) ~= ' ') then
          inlines:insert(i, pandoc.RawInline("html", "<span style=\"white-space: nowrap;\">"));
          inlines:insert(i+3,pandoc.RawInline("html", "</span>"));
        end
      end
      return inlines
    end,
    Header = function(header)
      header.content:insert(1,
        pandoc.RawInline("html", ("<a href=%q class=\"header-link\">"):format('#' .. header.identifier))
      );
      header.content:insert(
        pandoc.RawInline("html", ("<span class=\"header-link-emoji\">🔗</span></a>"):format('#' .. header.identifier))
      );
      return header;
    end
  },
  {
    Math = function(x)
      local t = 't'
      local command = "katex -f .macros -t"
      if x.mathtype == "DisplayMath" then
        command = command .. " -d"
        t = 'd'
      end

      if cache[t .. '$' .. x.text] then
        return pandoc.RawInline("html", cache[t .. '$' .. x.text])
      end

      local path = os.tmpname()
      print("Writing LaTeX to temporary file " .. path)
      local inp = io.open(path, "w")
      inp:write(trim(x.text))
      inp:close()

      print(("%s %q"):format(command, x.text))
      local proc = io.popen(command .. " -i " .. path, "r")
      local code = trim(proc:read("*a"))
      proc:close()

      add_to_cache(t, x.text, code)

      os.remove(path)

      return pandoc.RawInline("html", code)
    end,
    CodeBlock = function(elem)
      local quiver = false
      for k, v in pairs(elem.classes) do
        if v == "quiver" then
          quiver = true
          break
        end
      end

      if not quiver then return elem end

      local path = os.tmpname()
      print("Writing diagram to temporary file " .. path)
      local tmp = io.open(path, "w")
      tmp:write(elem.text)
      tmp:close()

      local p = io.popen("md5sum " .. path, "r")
      local hash = p:read("*all"):sub(1, -1):gsub("^(%w+).*$", "%1")
      p:close()

      if not os.execute(("stat _build/diagrams/%s.tex &>/dev/null"):format(hash)) then
        print(("cp '%s' _build/diagrams/%s.tex"):format(path, hash))
        os.execute(("cp '%s' _build/diagrams/%s.tex"):format(path, hash))
      end

      os.remove(path)

      makefile:write(("%s/%s.svg\n"):format(HTML_DIR, hash))
      makefile:flush()

      local classes = "diagram "
      for _, v in pairs(elem.classes) do
        classes = classes .. " " .. v
      end

      local img = ("<div class=diagram-container> <img title=%q src=\"%s.svg\" class=%q /> </div>"):format(elem.attributes.title or "commutative diagram", hash, classes)


      return pandoc.RawBlock("html", img)
    end
  },
  {
    Pandoc = function(elem)
      local cache_file = io.open("_build/tex_cache" .. NAME .. ".lua", 'w')
      cache_file:write("local cache = ...\n")
      for key, val in pairs(cache) do
        cache_file:write(("cache[%q] = %q;\n"):format(key, val))
      end
      cache_file:close()
      makefile:close()
    end
  }
}
