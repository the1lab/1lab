{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
module Filter.TagSoup.Elements where

import Control.Arrow
import Control.Lens

import Text.HTML.TagSoup.Tree
import Text.HTML.TagSoup

import {-# SOURCE #-} Filter.TagSoup
import Filter.TagSoup.TH
import Filter


defineElements [
  "html", "base", "head", "link", "meta", "style", "title", "body",
  "address", "article", "aside", "footer", "header", "hgroup", "main",
  "nav", "section", "search", "blockquote", "dd", "div", "dl", "dt",
  "figcaption", "figure", "hr", "li", "menu", "ol", "p", "pre", "ul",
  "a", "abbr", "b", "bdi", "bdo", "br", "cite", "code", "data_", "dfn",
  "em", "i", "kbd", "mark", "q", "rp", "rt", "ruby", "s", "samp",
  "small", "span", "strong", "sub", "sup", "time", "u", "var", "wbr",
  "area", "audio", "img", "map_", "track", "video", "embed", "iframe",
  "object", "picture", "portal", "source", "canvas", "noscript",
  "script", "del", "ins", "caption", "col", "colgroup", "table", "tbody",
  "td", "tfoot", "th", "thead", "tr", "button", "datalist", "fieldset",
  "form", "input", "label", "legend", "meter", "optgroup", "option",
  "output", "progress", "select", "textarea", "details", "dialog",
  "summary", "slot", "template", "acronym", "big", "center", "dir",
  "font", "frame", "frameset", "image", "marquee", "menuitem", "nobr",
  "noembed", "noframes", "param", "plaintext", "rb", "rtc", "strike",
  "tt", "xmp", "svg" ]
