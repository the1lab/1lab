// Copyright 2002-2010, Simon Marlow.  All rights reserved.
// https://github.com/haskell/haddock/blob/ghc-8.8/LICENSE
// Slightly modified by Tesla Ice Zhang

let links: Array<HTMLAnchorElement> = [], types: string[];
const paths: { module: string, baseURL: string, source: string } = window as any;

const showTimeout: number = 100, hideTimeout: number = 100;
const currentHovers: Map<HTMLElement, Hover> = new Map();

class Hover {
  private showTimer?: number;
  private hideTimer?: number;

  /* Used only to prevent re-renders */
  private shown: boolean = false;

  /* Is this mouse cursor currently in this element? */
  private anchored: boolean = false;

  private parents: Hover[] = [];
  private children: Hover[] = [];

  private fadeDirection: undefined | 'up' | 'down';

  constructor(private parent: HTMLElement, private element: HTMLDivElement, private animate: boolean) {
    currentHovers.set(parent, this);

    element.addEventListener("mouseenter", () => this.liven());
    element.addEventListener("mouseleave", () => this.kill());
  }

  private place() {
    const selfRect = this.parent.getBoundingClientRect();
    const hoverRect = this.element.getBoundingClientRect();

    if (selfRect.bottom + hoverRect.height + 48 > window.innerHeight) {
      // Tooltip placed above anchor
      this.element.style.top = `${window.scrollY + selfRect.top - hoverRect.height}px`;
      this.fadeDirection = 'down';
    } else {
      // Tooltip placed below anchor
      this.element.style.top = `${window.scrollY + selfRect.bottom}px`;
      this.fadeDirection = 'up';
    }

    if (selfRect.left + hoverRect.width > window.innerWidth) {
      this.element.style.left = `calc(${selfRect.right - hoverRect.width}px)`;
    } else {
      this.element.style.left = `${selfRect.left}px`;
    }

    if (this.animate)
      this.element.classList.add(`popup-fade-in-${this.fadeDirection}`);
  }

  public liven() {
    this.anchored = true;

    clearTimeout(this.hideTimer)
    if (this.shown) return;

    this.showTimer = setTimeout(() => {
      document.body.appendChild(this.element);
      this.place();
      this.shown = true;

      for (const [_, other] of currentHovers) {
        if (other === this) continue;
        if (other.element.contains(this.parent)) {
          this.parents.push(other);
          other.children.push(this);

          continue;
        };

        other.die();
      }

      refreshLinks();
    }, showTimeout);
  }

  private isAnchored(): boolean {
    if (this.anchored) return true;
    for (const e of this.children) {
      if (e.isAnchored()) return true;
    }
    return false;
  }

  private die() {
    // If this element or any of its children currently have the mouse,
    // then we don't do anything.
    if (this.isAnchored()) return;

    currentHovers.delete(this.parent);

    this.hideTimer = undefined;

    if (this.animate) {
      this.element.classList.remove(`popup-fade-in-${this.fadeDirection}`);
      this.element.classList.add(`popup-fade-out-${this.fadeDirection}`);

      setTimeout(() => {
        this.element?.remove();
      }, 300);
    } else {
      this.element?.remove();
    }

    // This might've been the last anchored child of its parent, so it
    // might die now.
    for (const e of this.parents) {
      e.die();
    }
  }

  public kill() {
    clearTimeout(this.showTimer);
    this.anchored = false;

    this.hideTimer = setTimeout(() => {
      this.die();
    }, hideTimeout);
  }
};


const page = window.location.pathname.slice(1).replace(".html", "");

async function fetchTypes(): Promise<string[]> {
  console.log("fetching types");

  const p = await fetch(`${paths.baseURL}/types/${paths.module}.json`, { method: 'get' });
  if (!p.ok) throw `Failed to load type-on-hover information for module ${paths.module}`;

  console.log(p);

  const out = await p.json();
  console.log(out);
  return out;
}

async function getHover(a: HTMLAnchorElement): Promise<Hover | undefined> {
  let target;
  const element = document.createElement("div");

  if (currentHovers.has(a)) return currentHovers.get(a);

  if (!Number.isNaN(target = Number.parseInt(a.getAttribute("data-identifier") ?? ""))) {
    if (!types) types = await fetchTypes();

    element.innerHTML = types[target]!;
    element.classList.add("hover-popup", "sourceCode");

    return new Hover(a, element, false);
  } else if (target = a.getAttribute("data-target")) {
    try {
      const p = await fetch(`${paths.baseURL}/fragments/${target}.html`, { method: 'get' });
      if (!p.ok) return;

      element.innerHTML = await p.text();
      element.classList.add("hover-popup");
      element.style.width = "24em";

      return new Hover(a, element, true);
    } catch (e) {
      console.log(e);
    }
  }

  return;
}


/* A `highlight` event contains:
 * `link`: HTMLAnchorElement | Node
 *   either a link or a node in the dependency graph
 * `on`: boolean
 *   whether to highlight or unhighlight
 */

document.addEventListener('highlight', (({ detail: { link } }: CustomEvent) => {
  let match: (a : HTMLAnchorElement) => boolean;

  if (link instanceof HTMLAnchorElement) {
    match = that => that.href === link.href;

    let hover: Hover | undefined;
    requestAnimationFrame(async () => {
      if ((hover = await getHover(link))) hover.liven();
    });

    link.addEventListener('mouseleave', function leave() {
      links.forEach(that => match(that) && that.classList.remove("hover-highlight"));

      if (hover) hover.kill();

      link.removeEventListener('mouseleave', leave);
    });

  } else {
    // Don't light up the entire page when hovering over the central node.
    if (link.id === page)
      return;

    match = that => that.pathname.slice(1).replace(".html", "") === link.id;
  }

  links.forEach(that => {
    if (match(that)) {
      that.classList.add("hover-highlight");
    }
  });
}) as EventListener);

export function refreshLinks() {
  links = Array.from(document.getElementsByTagName("a"));
  links.forEach(link => {
    if (link.hasAttribute("href")) {
      link.onmouseover = () => document.dispatchEvent(new CustomEvent('highlight', { detail: { link, on: true } }))
    }
  });
}

document.addEventListener("DOMContentLoaded", refreshLinks);

export {};
