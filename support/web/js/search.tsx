import { Searcher, MatchData } from "fast-fuzzy";
import { JSX, Content } from "./lib/jsx";

type SearchItem = {
  idIdent: string,
  idType: string,
  idAnchor: string,
};

const highlight = ({ match, original }: MatchData<SearchItem>): Content => {
  if (match.length == 0) return original;

  if (match.index == 0 && match.length == original.length) return <span class="search-match">{original}</span>;

  const out: Array<Content> = [];
  if (match.index > 0) out.push(original.substring(0, match.index));
  out.push(<span class="search-match">{original.substring(match.index, match.index + match.length)}</span>);
  out.push(original.substring(match.index + match.length));
  return out;
};

let loadingIndex = false;
let index: Searcher<SearchItem, { returnMatchData: true }> | null;

const startSearch = (mirrorInput: HTMLInputElement | null) => {
  if (document.getElementById("search-wrapper")) return;

  const searchInput = <input id="search-box" type="text" placeholder="Search..." autocomplete="off" tabindex="0" /> as HTMLInputElement;
  const searchResults = <div id="search-results"></div>;
  const searchWrapper = <div id="search-wrapper" class="modal open">
    <div class="modal-contents search-form" role="form">
      {searchInput}
      {searchResults}
    </div>
  </div>;

  const setError = (contents: string) => {
    searchResults.innerHTML = "";
    searchResults.appendChild(<span class="search-error">{contents}</span>);
  };

  const doSearch = () => {
    if (!index) return;

    const results = index.search(searchInput.value);

    if (results.length > 0) {
      searchResults.scrollTo(0, 0);
      searchResults.innerHTML = "";

      const list = <ul>
        {results.slice(0, 20).map(match => <li>
          <a class="search-result" href={`/${match.item.idAnchor}`}>
            <h3 class="sourceCode search-header">
              <span>
                {highlight(match)}
              </span>
              <span class="search-module">{match.item.idAnchor.replace(/#[0-9]+$/, "").slice(0,-".html".length)}</span>
            </h3>
            <p class="search-type sourceCode">{match.item.idType}</p>
          </a>
        </li>)}
      </ul>;


      searchResults.appendChild(list);
    } else if (searchInput.value.length === 0) {
      searchResults.innerHTML = "";
    } else {
      searchResults.innerText = "No results found";
    }
  };

  // Input handlers

  searchInput.addEventListener("input", () => {
    if (mirrorInput) mirrorInput.value = searchInput.value;
    doSearch();
  });

  // While searchInputProxy should never be focused for long, let's process those events anyway.
  const syncMirrorInput = () => {
    if (mirrorInput) searchInput.value = mirrorInput.value;
    searchInput.focus();
    doSearch();
  };
  if (mirrorInput) mirrorInput.addEventListener("input", syncMirrorInput);

  const closeSearch = () => {
    searchWrapper.remove()
    if (mirrorInput) mirrorInput.removeEventListener("input", syncMirrorInput);
  };

  searchWrapper.addEventListener("click", e => {
    if (e.target !== searchInput) closeSearch();
  });

  // Keyboard navigation through search items

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
  };

  const movePrevious = () => {
    const active = searchResults.querySelector("li.active");
    if (active && active.previousElementSibling) {
      removeActive(active);
      addActive(active.previousElementSibling);
    }
  };

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

  document.body.appendChild(searchWrapper);
  searchInput.focus();

  // Fetch the search index if not available and start searching
  if (!loadingIndex) {
    loadingIndex = true;
    fetch("/static/search.json")
      .then(r => r.json())
      .then(entries => {
        index = new Searcher(entries, {
          returnMatchData: true,
          keySelector: (x: SearchItem) => x.idIdent,
        });

        doSearch();
      })
      .catch(e => {
        console.error("Failed to load search index", e);
        loadingIndex = false;
        setError("Failed to load search index");
      });
  }

  doSearch();
}

document.addEventListener("DOMContentLoaded", () => {
  // Default pages have a "search" box which, when clicked, opens the main search box.
  const searchInputProxy = document.getElementById("search-box-proxy") as HTMLInputElement | null;
  if (searchInputProxy) {
    searchInputProxy.addEventListener("focus", () => startSearch(searchInputProxy));
  }

  // Allow pressing Ctrl+K to search anywhere.
  document.addEventListener("keydown", e => {
    if (e.key == "k" && e.ctrlKey && !e.altKey) {
      e.preventDefault();
      startSearch(searchInputProxy);
    }
  });
});
