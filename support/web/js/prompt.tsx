import { JSX } from "./lib/jsx";
import { isExact, type PromptItemResult, sortPromptItem } from "./prompt/items";
import { allSections } from "./prompt/sections";

// Components of the search box. These are always in the DOM.
const searchInput = <input id="search-box" type="text" placeholder="Search..." autocomplete="off" tabindex="0" /> as HTMLInputElement;

// Annoyingly, in addition to the input box itself, we need to keep
// track of all these bits. First, the result list, for.. adding search
// results;
const searchResults = <ul> </ul>;

// The actual search popup itself, to use for clipping later;
const searchContents =
  <div class="modal-contents search-form" role="form">
    {searchInput}
    <div id="search-results">
      {searchResults}
    </div>
  </div>

// And the overall modal, which we need to control the visibility and
// also to attach the opening/closing event.
const searchWrapper =
  <div id="search-wrapper" class="modal">
    {searchContents}
  </div>;

/** Unmark an element as being active. */
const removeActive = (elem: Element) => {
  elem.classList.remove("active");
  elem.ariaSelected = "false";
};

/** Mark an element as being active. */
const addActive = (elem: Element) => {
  elem.classList.add("active");
  elem.ariaSelected = "true";
  elem.scrollIntoView({
    block: "nearest",
  });
};

/** If an element is currently active, unmark it, and return the element;
 * If nothing is selected, this function has no effect. */
const unselect = (): Element | undefined => {
  const active = searchResults.querySelector("li.active");
  if (!active) return;
  removeActive(active);
  return active;
}

/** Indicates whether the mouse has been moved since the last time the
 * user has used the keyboard to change the active item. */
let mouseSelection = true;

const itemAfter = (item: Node) =>
  document.evaluate("following-sibling::li[@class=\"search-item\"][1]", item, null,
    XPathResult.FIRST_ORDERED_NODE_TYPE).singleNodeValue

const itemBefore = (item: Node) =>
  document.evaluate("preceding-sibling::li[@class=\"search-item\"][1]", item, null,
    XPathResult.FIRST_ORDERED_NODE_TYPE).singleNodeValue

const sectionBefore = (item: Node) =>
  document.evaluate("preceding-sibling::li[@class=\"search-header\"][2]", item, null,
    XPathResult.FIRST_ORDERED_NODE_TYPE).singleNodeValue

const sectionAfter = (item: Node) =>
  document.evaluate("following-sibling::li[@class=\"search-header\"][1]", item, null,
    XPathResult.FIRST_ORDERED_NODE_TYPE).singleNodeValue

/** Select the next item. */
const moveNext = () => {
  const active = unselect();
  let next;
  mouseSelection = false;

  const top = () => {
    const elem = searchResults.querySelector("li.search-item");
    if (elem) addActive(elem);
  };

  if (!active) {
    top();
  } else if ((next = itemAfter(active)) instanceof Element) {
    addActive(next);
  }
};

/** Select the previous item. */
const movePrevious = () => {
  const active = searchResults.querySelector("li.active");
  let next;
  mouseSelection = false;

  if (active && (next = itemBefore(active)) instanceof Element) {
    removeActive(active);
    addActive(next);
  } else if (active && !next) {
    console.log("No previous item!");
    searchResults.parentElement?.scrollTo(0, 0);
  }
};

const moveNextSection = () => {
  const active = searchResults.querySelector("li.active");
  if (!active) return moveNext();
  let nexts, next;
  mouseSelection = false;

  if ((nexts = sectionAfter(active)) instanceof Element && (next = itemAfter(nexts)) instanceof Element) {
    removeActive(active);
    addActive(next);
  }
};

const movePreviousSection = () => {
  const active = searchResults.querySelector("li.active");
  let nexts, next;
  mouseSelection = false;

  if (active && (nexts = sectionBefore(active)) instanceof Element && (next = itemAfter(nexts)) instanceof Element) {
    removeActive(active);
    nexts.scrollIntoView();
    addActive(next);
  }
};

/** Close the search box. Unsets the selected item, if any. */
export const closeSearch = () => {
  unselect();

  searchWrapper.classList.remove("open")
};


/** Create the element corresponding to a given {@link PromptItemResult}.
 * Also connects the event handlers for selecting and activating this
 * item. */
const renderItem = ({ item, original, match }: PromptItemResult) => {
  const li =
    <li class="search-item">
      <a class="search-result">
        {item.render(original, match)}
      </a>
    </li>;

  li.addEventListener("mouseover", () => {
    if (!mouseSelection) return;

    unselect();
    addActive(li);
  });

  li.addEventListener("mousemove", () => {
    mouseSelection = true;

    unselect();
    addActive(li);
  });

  li.onclick = () => {
    if (item.activate() === 'close') {
      closeSearch()
    } else {
      li.replaceChildren(
        <a class="search-result">
          {item.render(original, match)}
        </a>);
    };
  };

  return li;
};

let searchTask: number = 0;

class DeferredItems {
  private readonly results: PromptItemResult[];
  private readonly task: number;
  private readonly query: string;
  private writeHead: HTMLElement;

  private readHead: number = 0;
  private batchSize: number = 128;

  constructor (r: PromptItemResult[], h: HTMLElement, t: number, q: string) {
    this.results   = r;
    this.writeHead = h;
    this.task = t;
    this.query = q;
  }

  public trigger() {
    let last: HTMLElement = this.writeHead;
    if (this.task !== searchTask || this.readHead >= this.results.length) return

    const lim = Math.min(this.results.length, this.readHead + this.batchSize);
    console.log(`Rendering deferred batch of ${lim - this.readHead} results for "${this.query}"`);

    for (let i = this.readHead; i < lim; i++) {
      const elt = renderItem(this.results[i]);
      last.insertAdjacentElement('afterend', elt);
      last = elt;
    }

    this.writeHead = last;
    this.readHead = this.readHead + this.batchSize, this.batchSize = Math.min(512, this.batchSize * 2);

    window.requestAnimationFrame(() => { this.trigger() });
  }
}

/** Perform and render the results of a query. */
const doSearch = (search: string) => {
  const rendered: HTMLElement[] = [];
  const task = ++searchTask;

  if (search === "") {
    allSections.forEach(s => {
      const es = s.defaultEntries();
      if (es.length <= 0) return;
      rendered.push(s.header);
      es.forEach(i => rendered.push(renderItem(i)));
    });
  } else {
    const exacts: PromptItemResult[] = [];

    allSections.forEach(s => {
      const results: PromptItemResult[] = [];
      s.doSearch(search).forEach(e => isExact(search, e) ? exacts.push(e) : results.push(e));
      if (results.length === 0) return;

      rendered.push(s.header);

      let now = results.slice(0, 32).map(renderItem);
      rendered.push(...now);

      const later = new DeferredItems(results.slice(32), now[now.length - 1], task, search);
      window.setTimeout(() => later.trigger(), 200);
    });

    if (exacts.length > 0) {
      rendered.unshift(...exacts.sort(sortPromptItem(search)).map(renderItem));
      rendered.unshift(<li class="search-header">Exact matches</li>);
    }
  }

  // We replace the children atomically down here to prevent flashing.
  searchResults.replaceChildren(...rendered);
  searchResults.parentElement?.scrollTo(0, 0);
}

// That was the hard part, now we just need to connect some event
// handlers.

searchInput.addEventListener("input", () => {
  doSearch(searchInput.value);
});

let searchReady = false, searchPending = false;
document.addEventListener("searchready", () => {
  searchReady = true;
  if (searchPending) {
    searchPending = false;
    window.requestAnimationFrame(() => startSearch());
  }
});

const startSearch = () => {
  if (!searchReady) {
    searchPending = true;
    return;
  }

  mouseSelection = true;
  searchInput.value = '';

  searchWrapper.classList.add("open");
  searchInput.focus();

  doSearch(searchInput.value);
};

const isSearching = () => searchWrapper.classList.contains("open");

searchWrapper.addEventListener("click", e => {
  const cts = searchContents.getBoundingClientRect();
  let fake = e.clientX === 0 && e.clientY === 0;
  let inside =
    (e.clientX > cts.left && e.clientX < cts.right) &&
    (e.clientY > cts.top && e.clientY < cts.bottom);
  if (!inside && !fake) { closeSearch(); return; }
});

document.addEventListener("DOMContentLoaded", () => {
  document.body.appendChild(searchWrapper);

  searchInput.addEventListener("keydown", (e) => {
    switch (e.key) {
      case "Tab":
        e.preventDefault();
        if (e.shiftKey) movePrevious(); else moveNext();
        break;

      case "Down":
      case "ArrowDown":
        e.preventDefault();
        moveNext();
        break;

      case "Up":
      case "ArrowUp":
        e.preventDefault();
        movePrevious();
        break;

      case "Left":
      case "ArrowLeft":
        if (!e.ctrlKey) return;
        e.preventDefault();
        movePreviousSection();
        break;

      case "Right":
      case "ArrowRight":
        if (!e.ctrlKey) return;
        e.preventDefault();
        moveNextSection();
        break;

      case "Enter": {
        e.preventDefault();

        const link: HTMLAnchorElement | null = searchResults.querySelector("li.active > a.search-result");
        link?.click();
        break;
      }
    }
  });

  const searchInputProxy = document.getElementById("search-box-proxy") as HTMLInputElement | null;
  if (searchInputProxy) {
    searchInputProxy.addEventListener("focus", () => startSearch());
  }

  document.addEventListener("keydown", e => {
    if (e.key == "k" && e.ctrlKey && !e.altKey) {
      e.preventDefault();
      if (isSearching()) {
        closeSearch();
      } else {
        startSearch();
      };
    } else if (e.key === "Escape" && isSearching()) {
      e.preventDefault();
      closeSearch();
    }
  });
});

export { };
