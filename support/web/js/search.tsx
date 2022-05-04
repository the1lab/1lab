import { Searcher, MatchData } from "fast-fuzzy";
import { JSX } from './lib/jsx';

type SearchItem = {
  idIdent: string,
  idType: string,
  idAnchor: string,
}

const createElem = (tag: string, classes: Array<string>, contents: string | Array<Node> | Node) => {
  const elem = document.createElement(tag);
  if (typeof contents === "string") {
    elem.innerText = contents;
  } else if (contents instanceof Array) {
    for (const child of contents) elem.appendChild(child);
  } else {
    elem.appendChild(contents);
  }
  for (const cls of classes) elem.classList.add(cls);
  return elem;
};

const highlight = ({ match, original }: MatchData<SearchItem>): Node | Array<Node> => {
  if (match.length == 0) return document.createTextNode(original);

  if (match.index == 0 && match.length == original.length) return createElem("span", ["search-match"], original);

  const out: Array<Node> = [];
  if (match.index > 0) out.push(document.createTextNode(original.substring(0, match.index)));
  out.push(createElem("span", ["search-match"], original.substring(match.index, match.index + match.length)));
  out.push(document.createTextNode(original.substring(match.index + match.length)));
  return out;
};

document.addEventListener('DOMContentLoaded', () => {

  const searchInputProxy = document.getElementById("search-box-proxy") as HTMLInputElement;

  const searchWrapper = document.getElementById("search-wrapper") as HTMLDivElement;
  const searchInput = document.getElementById("search-box") as HTMLInputElement;
  const searchResults = document.getElementById("search-results") as HTMLDivElement;

  let loadingIndex = false;
  let index: Searcher<SearchItem, { returnMatchData: true }> | null;

  const setError = (contents: string) => {
    searchResults.innerHTML = "";

    const child = document.createElement("div");
    child.classList.add("search-error");
    child.innerText = contents;

    searchResults.appendChild(child);
  };

  const doSearch = () => {
    if (!index) return;

    const results = index.search(searchInput.value);

    if (results.length > 0) {
      searchResults.scrollTo(0, 0);
      searchResults.innerHTML = "";

      const list = <ul>
        {results.slice(0,20).map(match => {
          return <li>
              <a class="search-result" href={`/${match.item.idAnchor}`}>
              <h3 class="sourceCode">{ highlight(match) }</h3>
              <p class="search-type sourceCode">{match.item.idType}</p>
              <p class="search-module">
                Defined in {match.item.idAnchor.replace(/#[0-9]+$/, "")}
              </p>
            </a>
          </li>;
        })}
      </ul>

      searchResults.appendChild(list);
    } else if (searchInput.value.length === 0) {
      searchResults.innerHTML = "";
    } else {
      searchResults.innerText = "No results found";
    }
  };

  const closeSearch = () => {
    searchWrapper.classList.remove("open");
    searchInput.blur();
  }

  searchWrapper.addEventListener("click", (e) => {
    if (e.target !== searchInput) closeSearch();
  });

  const startSearch = () => {
    searchWrapper.classList.add("open");
    // Because the element isn't visible, we need to focus it later. I know, it's gross.
    setTimeout(() => searchInput.focus(), 100);

    if (!loadingIndex) {
      loadingIndex = true;
      fetch("/static/search.json")
        .then((r) => r.json())
        .then((entries) => {
          index = new Searcher(entries, {
            returnMatchData: true,
            keySelector: (x: SearchItem) => x.idIdent,
          });

          doSearch();
        })
        .catch((e) => {
          console.error("Failed to load search index", e);
          loadingIndex = false;
          setError("Failed to load search index");
        });
    }

    doSearch();
  };

  searchInputProxy.addEventListener("focus", startSearch);

  document.addEventListener("keydown", e => {
    // Allow pressing Ctrl+K to focus the input box.
    if (e.key == "k" && e.ctrlKey && !e.altKey) {
      e.preventDefault();
      startSearch();
    }
  });

  const removeActive = (elem: Element) => {
    elem.classList.remove("active");
    elem.ariaSelected = "false";
  };
  const addActive = (elem: Element) => {
    elem.classList.add("active");
    elem.ariaSelected = "true";
    elem.scrollIntoView({
      block: "nearest",
    });
  };

  const moveNext = () => {
    const active = searchResults.querySelector("li.active");
    if (!active) {
      const elem = searchResults.querySelector("li");
      if (elem) addActive(elem);
    } else if (active.nextElementSibling) {
      removeActive(active);
      addActive(active.nextElementSibling);
    }
  }

  const movePrevious = () => {
    const active = searchResults.querySelector("li.active");
    if (active && active.previousElementSibling) {
      removeActive(active);
      addActive(active.previousElementSibling);
    }
  }

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

      case "Enter": {
        e.preventDefault();

        const link: HTMLAnchorElement | null =
          searchResults.querySelector("li.active > a") || searchResults.querySelector("li > a");
        if (link) link.click();
        break;
      }

      case "Escape": {
        e.preventDefault();
        closeSearch();
        break;
      }
    }
  });

  searchInput.addEventListener("input", () => {
    searchInputProxy.value = searchInput.value;
    doSearch();
  });

  // While searchInputProxy should never be focused for long, let's process those events anyway.
  searchInputProxy.addEventListener("input", () => {
    searchInput.value = searchInputProxy.value;
    searchInput.focus();
    doSearch();
  })
});
