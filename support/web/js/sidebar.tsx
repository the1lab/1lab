document.addEventListener('DOMContentLoaded', () => {
  const headers = Array.from(document.querySelectorAll("article a.header-link"))
    .map(x => x.parentElement)
    .filter((x): x is HTMLHeadingElement => !!x);

  const headerLinks = Array.from(document.querySelectorAll("aside#toc a.header-link"));

  const findHeader = () => {
    let closest = headers[0];

    for (const header of headers) {
      let top = header.getBoundingClientRect().top;
      if (top >= 25) break;
      closest = header;
    };

    for (const link of headerLinks) {
      if (link.getAttribute("href") === `#${closest.getAttribute("id")}`) {
        link.classList.add("current-heading");
      } else {
        link.classList.remove("current-heading");
      }
    }
  };

  let waiting = false;

  document.addEventListener("scroll", () => {
    if (!waiting) {
      window.requestAnimationFrame(() => {
        findHeader();
        waiting = false;
      });
      waiting = true;
    }
  });

  setTimeout(() => { findHeader() }, 200);
});
export { };
