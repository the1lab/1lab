const neighbourCache = {};

const neighbours = (node, links) => {
  if (neighbourCache[node.id]) {
    return neighbourCache[node.id];
  }
  const nbh = new Set();
  for (const link of links) {
    if (link[0] === node) {
      nbh.add(link[1]);
    } else if (link[1] === node) {
      nbh.add(link[0]);
    } else if (link.source === node && !link.isGravity) {
      nbh.add(link.target);
    } else if (link.target === node && !link.isGravity) {
      nbh.add(link.source);
    }
  }
  neighbourCache[node.id] = nbh;
  return nbh;
}

const page = (() => {
  if (window.location.pathname === "/") {
    return "index.html"
  } else {
    return window.location.pathname.slice(1, -5);
  }
})();

const nbhoodSubgraph = (node, links) => {
  const nodes = neighbours(node, links);
  const edges = [];

  for (const link of links) {
    if (nodes.has(link[0]) && nodes.has(link[1])) {
      edges.push({
        source: link[0],
        target: link[1],
        primary: (link[0] === node || link[1] === node)
      });
    }
  }

  return {
    nodes: Array(...nodes).map(x => ({
      id: x,
      radius: x === page ? 15 : 10,
    })),
    edges: edges
  };
}

// Compute a hue based on the string's SHA-2 hash. Overkill? Yeah,
// maybe.
const encoder = new TextEncoder();
const stringHue = async (message) => {
  let i = 0;
  for (const c of message) {
    i += i*31 + c.charCodeAt(0)
  }
  return i % 359;
}

const hsvToCss = (h,s,v) => {
  const f = (n,k=(n+h/60)%6) => v - v*s*Math.max( Math.min(k,4-k,1), 0);
  const col = [f(5),f(3),f(1)].map(x=>x*255|0).join(', ')
  return "rgb(" + col + ")";
}

const makeColours = async (arr) => {
  // Populate the section and colour for each node.
  for (const x of arr) {
    const sections = x.id.split('.')
    x.section = sections.slice(0,2).join(',');

    const hue = await stringHue(x.section);
    x.colour = hsvToCss(hue, 0.5, 0.83);
  }
}

const render = (nodes, lines, labels) => () => {
  // Re-position the nodes
  nodes
    .attr('cx', d => d.x)
    .attr('cy', d => d.y)
    .attr('fill', d => d.colour);

  lines
    // Re-position the edges
    .attr("x1", d => d.source.x)
    .attr("y1", d => d.source.y)
    .attr("x2", d => d.target.x)
    .attr("y2", d => d.target.y)
    // Control edge visibility:
    .attr("visibility", d => {
      if (d.isGravity) return 'hidden'; // Gravity is never shown

      // Show edges to/from a hovered node, and always show primary
      // edges
      if (d.primary || d.source.hover || d.target.hover) {
        return '';
      }
      return 'hidden';
    })
    .attr("stroke", d => {
      // Change edge colour depending on the endpoints being hovered or
      // not.
      if (d.source.hover) { return d.source.colour; }
      if (d.target.hover) { return d.target.colour; }
      return '#ddd';
    });

  labels
    .attr('transform', d => `translate(${d.x+d.radius}, ${d.y-5})`)
    .attr('visibility', d => {
      if (d.id === page || d.hover) {
        return '';
      }
      return 'hidden';
    });
};

const clamp = (x, lo, hi) =>
  x < lo ? lo : x > hi ? hi : x;

const resize = (sim) => {
  let last_width;
  const gravity = d3.forceCenter();
  sim.force('center', gravity);
  const svgEl = document.querySelector("aside#toc svg");

  // This observer watches for changes in the SVG size box and
  // re-computes the coordinates of the centering force.
  return new ResizeObserver(entries => {
    for (const entry of entries) {
      const box = svgEl.getBoundingClientRect();
      const width = box.width, height = box.height;

      if (last_width === width) { return; }
      last_width = width;

      gravity.x(width / 2).y(height / 2);
      sim.width = width;
      sim.height = height;
      sim.alpha(1).restart();
    }
  });
};

const navigateTo = (ev, d) => {
  window.location.pathname = `/${d.id}.html`;
};

const modal = (close = ()=>{}) => {
  if (Array(...document.querySelectorAll("div.modal.open")).length >= 1) {
    return;
  }

  // Create the open modal dialog box. This is just the backing
  // background!
  const dialog = document.createElement("div");
  dialog.classList.add("modal", "open");
  document.body.appendChild(dialog);

  // Create the container to hold the header and network
  const inside = document.createElement("div");
  inside.classList.add("modal-contents")
  dialog.appendChild(inside);

  // Header
  const header = document.createElement("h3");
  header.innerText = `Module dependency graph for ${page}`;
  inside.appendChild(header);

  // Instructions
  inside.appendChild(document.createTextNode("(Click outside the dialog to dismiss, double click on a node to navigate there)"));

  // Steal the SVG from the sidebar
  const svg = document.querySelector("aside#toc svg");
  inside.appendChild(svg);

  const parent = document.querySelector("aside#toc > div#toc-container");

  dialog.addEventListener("click", (ev) => {
    // On close, re-parent the SVG to the sidebar
    if (ev.target === dialog) {
      parent.appendChild(svg);
      dialog.remove();
      close();
    }
  });
};

document.addEventListener('DOMContentLoaded', async () => {
  const data = (await fetch("/static/links.json").then(r => r.json())).slice(0, -1);
  const { nodes, edges } = nbhoodSubgraph(page, data);
  await makeColours(nodes);
  window.nodes = nodes;

  // If there's no graph for this page, we don't append a SVG or
  // anything.
  if (edges.length <= 0) return;

  // We add a "gravity" link between each pair of nodes in the same
  // section to make "connected components" (not actually --- just
  // modules in the same section) cluster up.
  for (const n1 of nodes) {
    for (const n2 of nodes) {
      // XXX: Don't add gravity links between the primary and its orbits
      if (n1.section === n2.section && n1.id !== page && n2.id !== page) {
        edges.push({
          source: n1,
          target: n2,
          isGravity: true
        });
      }
    }
  }

  // Force rendering simulation.
  const sim = d3.forceSimulation(nodes)
    // Repellent force. Nodes in the simulation VERY STRONGLY repel
    // eachother.
    .force('charge', d3.forceManyBody().strength(d => d.id === page ? -500 : -200))
    // Link force. Links are edges from the graph /or/ the "gravity"
    // edges we added above.
    .force('link', d3.forceLink(edges)
      .id(d => d.id)
      .strength(d => {
        // Gravity links are stronger than other types of links. This
        // makes nodes with the same colour "cluster up".
        if (d.isGravity) return 0.5;
        return 0.3;
      })
      .distance(d => {
        if (d.isGravity) return 30;
        if (d.source.section === d.target.section) return 30;
        return 80;
      }))
    .force('collision', d3.forceCollide().radius(d => d.radius));

  // Allocate new zoom behaviour
  const zoom = d3.zoom();

  const container = document.querySelector("aside#toc > div#toc-container");
  const ruler = container.appendChild(document.createElement("hr"));

  // Create the SVG element and add a <g>roup for the zoom
  // transformation.
  const svg = d3
    .select("aside#toc > div#toc-container")
    .append('svg')
    .call(zoom)
    .append('g');

  zoom.on('zoom', ({transform: tr}) => {
    svg.attr("transform", `translate(${tr.x}, ${tr.y}) scale(${tr.k})`);
  });

  // Draw the edges
  const lines = svg.selectAll('line')
    .data(edges)
    .join('line')
    .attr('stroke', '#ccc');

  // Draw the circles representing the nodes. At this point, we have
  // already populated each nodes' colour, section and radius.
  const circles = svg.selectAll('circle')
    .data(nodes)
    .join('circle')
    .attr('r', d => d.radius)
    .attr('fill', d => d.colour);

  // Draw the label containers (this is a group that gets translated
  // into place). This is what is actually controlled by the render
  // callback: the text elements keep their position fixed (relative to
  // the <g>roups, which are translated).
  const labels =
    svg.selectAll('g')
      .data(nodes)
      .join('g');

  // Append to each group the label and the white backing for it.
  labels
    .append('text')
    .text(d => d.id)
    .clone(true).lower()
    .attr('fill', 'none')
    .attr('stroke', 'white')
    .attr('stroke-width', 2);

  const renderCallback = render(circles, lines, labels);
  window.renderCallback = renderCallback;
  window.edges = edges;
  sim.on('tick', renderCallback);

  // Create the resize observer to automatically change the centering
  // force when the SVG size changes (e.g. when the window is resized or
  // the modal is maximised).
  resize(sim).observe(document.querySelector("aside#toc svg"));

  const drag = d3.drag().on("start", (event, d) => {
    d.fx = d.x;
    d.fy = d.y;
  }).on("drag", (event, d) => {
    d.fx = clamp(event.x, 0, sim.width);
    d.fy = clamp(event.y, 0, sim.height);
    sim.alpha(1).restart();
  });
  circles.call(drag);

  // Toggle visibility of the label on hover.
  circles.on('mouseenter', (ev, d) => {
    d.hover = true;
    if (d.id !== page) {
      for (const n of neighbours(d, edges)) {
        n.saved = n.colour;
        n.colour = d.colour;
      }
    }
    renderCallback();
  }).on('mouseleave', (ev, d) => {
    d.hover = false;
    for (const n of neighbours(d, edges)) {
      if (n.saved !== undefined) {
        n.colour = n.saved;
        delete n.saved;
      }
    }
    renderCallback();
  });

  // Make sure that hovering on the label keeps it shown, otherwise
  // hovering your cursor between the circle and the label causes the
  // label to flash rapidly
  labels.on('mouseenter', (ev, d) => {
    d.hover = true;
    if (d.id !== page) {
      for (const n of neighbours(d, edges)) {
        n.saved = n.colour;
        n.colour = d.colour;
      }
    }
    renderCallback();
  }).on('mouseleave', (ev, d) => {
    d.hover = false;
    for (const n of neighbours(d, edges)) {
      if (n.saved !== undefined) {
        n.colour = n.saved;
        delete n.saved;
      }
    }
    renderCallback();
  });

  // Navigate to on double click
  circles.on("dblclick", navigateTo);
  labels.on("dblclick", navigateTo);

  let addExpand;
  const reset = () => {
    // Reset zoom level
    svg.transition().duration(750).call(zoom.transform, d3.zoomIdentity);
    // Clear all forced coordinates
    for (const n of nodes) {
      n.fx = null;
      n.fy = null;
    }
    // Re-center
    sim.alpha(1).restart();
  }

  addExpand = () => {
    const expand = document.createElement("button");

    ruler.style.display = "block";
    expand.innerText = "Maximise network"
    expand.style.display = 'inline-block';

    expand.addEventListener("click", () => {
      ruler.style.display = "none";
      expand.remove();
      modal(addExpand);
      reset();
    });

    reset();
    container.appendChild(expand);
  };

  addExpand();
});
