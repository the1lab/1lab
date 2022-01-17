// Copyright 2002-2010, Simon Marlow.  All rights reserved.
// https://github.com/haskell/haddock/blob/ghc-8.8/LICENSE
// Slightly modified by Tesla Ice Zhang

let links = [];

let currentHover = null;

const highlight = (self, on) => () => {
  const type = self.getAttribute("data-type");
  if (type) {
    if (currentHover) {
      currentHover.remove();
      currentHover = null;
    }

    if (on) {
      currentHover = document.createElement("div");
      currentHover.innerText = type;
      currentHover.classList.add("typeTooltip", "sourceCode");
      currentHover.style.top = `${self.offsetTop + self.offsetHeight}px`;
      currentHover.style.left = `${self.offsetLeft}px`;
      document.body.appendChild(currentHover);
      console.log(currentHover);
    }
  }


  links.forEach(that => {
    if (self.href != that.href) {
      return;
    }

    if (on) {
      that.classList.add("hover-highlight");
    } else {
      that.classList.remove("hover-highlight");
    }
  });
};

document.addEventListener("DOMContentLoaded", async () => {
  links = Array(...document.getElementsByTagName("a"));
  links.forEach(link => {
    if (link.hasAttribute("href")) {
      link.onmouseover = highlight(link, true);
      link.onmouseout = highlight(link, false);
    }
  });
});
