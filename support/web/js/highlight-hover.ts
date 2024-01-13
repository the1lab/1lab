// Copyright 2002-2010, Simon Marlow.  All rights reserved.
// https://github.com/haskell/haddock/blob/ghc-8.8/LICENSE
// Slightly modified by Tesla Ice Zhang

let links: Array<HTMLAnchorElement> = [];

let currentHover: HTMLDivElement | null = null;

const page = window.location.pathname.slice(1).replace(".html", "");

/* A `highlight` event contains:
 * `link`: HTMLAnchorElement | Node
 *   either a link or a node in the dependency graph
 * `on`: boolean
 *   whether to highlight or unhighlight
 */

document.addEventListener('highlight', (({ detail: { link, on } }: CustomEvent) => {
  let match: (a : HTMLAnchorElement) => boolean;

  if (link instanceof HTMLAnchorElement) {
    const type = link.getAttribute("data-type");
    if (type) {
      if (currentHover) {
        currentHover.remove();
        currentHover = null;
      }

      if (on) {
        currentHover = document.createElement("div");
        currentHover.innerText = type;
        currentHover.classList.add("type-tooltip", "sourceCode");
        document.body.appendChild(currentHover);

        const selfRect = link.getBoundingClientRect();
        const hoverRect = currentHover.getBoundingClientRect();
        // If we're close to the bottom of the page, push the tooltip above instead.
        // The constant here is arbitrary, because trying to convert em to px in JS is a fool's errand.
        if (selfRect.bottom + hoverRect.height + 30 > window.innerHeight) {
          // 2em from the material mixin. I'm sorry
          currentHover.style.top = `calc(${link.offsetTop - hoverRect.height}px - 1em`;
        } else {
          currentHover.style.top = `${link.offsetTop + (link.offsetHeight / 2)}px`;
        }
        currentHover.style.left = `${link.offsetLeft}px`;
      }
    }
    match = that => that.href === link.href;
  } else {
    // Don't light up the entire page when hovering over the central node.
    if (link.id === page)
      return;

    match = that => that.pathname.slice(1).replace(".html", "") === link.id;
  }

  links.forEach(that => {
    if (match(that)) {
      if (on)
        that.classList.add("hover-highlight");
      else
        that.classList.remove("hover-highlight");
    }
  });
}) as EventListener);

document.addEventListener("DOMContentLoaded", async () => {
  links = Array.from(document.getElementsByTagName("a"));
  links.forEach(link => {
    if (link.hasAttribute("href")) {
      link.onmouseover = () => document.dispatchEvent(new CustomEvent('highlight', { detail: { link, on: true } }))
      link.onmouseout = () => document.dispatchEvent(new CustomEvent('highlight', { detail: { link, on: false } }))
    }
  });
});

export {};
