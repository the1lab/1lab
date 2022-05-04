document.addEventListener('DOMContentLoaded', () => {
  "use strict";

  const searchInputProxy = document.getElementById("search-box-proxy");

  const searchWrapper = document.getElementById("search-wrapper");
  const searchInput = document.getElementById("search-box");
  const searchResults = document.getElementById("search-results");

  let loadingIndex = false;
  let index;

  const setError = (contents) => {
    searchResults.innerHTML = "";

    const child = document.createElement("div");
    child.classList.add("search-error");
    child.innerText = contents;

    searchResults.appendChild(child);
  };

  const createElem = (tag, classes, contents) => {
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

  const highlight = (match, field) => {
    const ourMatch = match.matches.find((x) => x.key === field);
    if (!ourMatch) return match.item[field];

    const { value, indices } = ourMatch;

    const out = [];
    let lastIdx = 0;
    for (const [start, end] of indices) {
      if (lastIdx < start) out.push(document.createTextNode(value.substring(lastIdx, start)));
      out.push(createElem("span", ["search-match"], value.substring(start, end + 1)));
      lastIdx = end + 1;
    }
    if (lastIdx < value.length) {
      out.push(document.createTextNode(value.substring(lastIdx, value.length)));
    }

    return out;
  };

  const doSearch = () => {
    if (!index) return;

    const results = index.search(searchInput.value, { expand: true });
    if (results.length > 0) {
      searchResults.scrollTo(0, 0);
      searchResults.innerHTML = "";

      let i = 0;
      const list = document.createElement("ul");
      for (const result of results) {
        if (++i > 20) break; // Limit our results to 20.

        const entry = index.documentStore.getDoc(result.ref);

        const link = document.createElement("a");
        link.classList.add("search-result");
        link.href = `/${entry.idAnchor}`;

        link.appendChild(createElem("h3", ["sourceCode"], entry.idIdent));
        link.appendChild(createElem("p", ["search-type", "sourceCode"], entry.idType));
        link.appendChild(createElem("p", ["search-module"], `Defined in ${entry.idAnchor.replace(/#[0-9]+$/, "")}`));

        const elem = document.createElement("li");
        elem.appendChild(link);
        list.appendChild(elem);
      }

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
          index = elasticlunr(function () {
            this.addField('idIdent');
          });

          for (let i = 0; i < entries.length; i++) {
            const entry = entries[i];
            entry.id = i;
            index.addDoc(entry);
          }

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
      searchInputProxy.focus();
    }
  });

  const removeActive = (elem) => {
    elem.classList.remove("active");
    elem.ariaSelected = false;
  };
  const addActive = (elem) => {
    elem.classList.add("active");
    elem.ariaSelected = true;
    elem.scrollIntoView({
      block: "nearest",
    });
  };

  const moveNext = () => {
    const active = searchResults.querySelector("li.active");
    if (!active) {
      const elem = searchResults.querySelector("li");
      if (elem) addActive(elem);
    } else if (active.nextSibling) {
      removeActive(active);
      addActive(active.nextSibling);
    }
  }

  const movePrevious = () => {
    const active = searchResults.querySelector("li.active");
    if (active && active.previousSibling) {
      removeActive(active);
      addActive(active.previousSibling);
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

        const link =
          searchResults.querySelector("li.active > a") || searchResults.querySelector("li > a");
        if (link) link.click();
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
