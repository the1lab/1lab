{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
module Filter.TagSoup.Attributes where

import Control.Arrow
import Control.Lens

import Text.HTML.TagSoup.Tree
import Text.HTML.TagSoup

import {-# SOURCE #-} Filter.TagSoup
import Filter.TagSoup.TH
import Filter

defineAttributes [
  "accept" , "acceptCharset" , "accesskey" , "action" , "alt" ,
  "async" , "autocomplete" , "autofocus" , "autoplay" , "challenge" ,
  "charset" , "checked" , "cite" , "class_" , "cols" , "colspan" ,
  "content" , "contenteditable" , "contextmenu" , "controls" ,
  "coords" , "data_" , "datetime" , "defer" , "dir" , "disabled" ,
  "draggable" , "enctype" , "for" , "form" , "formaction" ,
  "formenctype" , "formmethod" , "formnovalidate" , "formtarget" ,
  "headers" , "height" , "hidden" , "high" , "href" , "hreflang" ,
  "httpEquiv" , "icon" , "id_" , "ismap" , "item" , "itemprop" ,
  "itemscope" , "itemtype" , "keytype" , "label" , "lang" , "list" ,
  "loop" , "low" , "manifest" , "max" , "maxlength" , "media" ,
  "method" , "min" , "multiple" , "name" , "novalidate" ,
  "onbeforeonload" , "onbeforeprint" , "onblur" , "oncanplay" ,
  "oncanplaythrough" , "onchange" , "onclick" , "oncontextmenu" ,
  "ondblclick" , "ondrag" , "ondragend" , "ondragenter" ,
  "ondragleave" , "ondragover" , "ondragstart" , "ondrop" ,
  "ondurationchange" , "onemptied" , "onended" , "onerror" , "onfocus"
  , "onformchange" , "onforminput" , "onhaschange" , "oninput" ,
  "oninvalid" , "onkeydown" , "onkeyup" , "onload" , "onloadeddata" ,
  "onloadedmetadata" , "onloadstart" , "onmessage" , "onmousedown" ,
  "onmousemove" , "onmouseout" , "onmouseover" , "onmouseup" ,
  "onmousewheel" , "ononline" , "onpagehide" , "onpageshow" ,
  "onpause" , "onplay" , "onplaying" , "onprogress" , "onpropstate" ,
  "onratechange" , "onreadystatechange" , "onredo" , "onresize" ,
  "onscroll" , "onseeked" , "onseeking" , "onselect" , "onstalled" ,
  "onstorage" , "onsubmit" , "onsuspend" , "ontimeupdate" , "onundo" ,
  "onunload" , "onvolumechange" , "onwaiting" , "open" , "optimum" ,
  "pattern" , "ping" , "placeholder" , "preload" , "pubdate" ,
  "radiogroup" , "readonly" , "rel" , "required" , "reversed" , "role"
  , "rows" , "rowspan" , "sandbox" , "scope" , "scoped" , "seamless" ,
  "selected" , "shape" , "size" , "sizes" , "span" , "spellcheck" ,
  "src" , "srcdoc" , "start" , "step" , "style" , "subject" ,
  "summary" , "tabindex" , "target" , "title" , "type_" , "usemap" ,
  "value" , "width" , "wrap" , "xmlns" ]
