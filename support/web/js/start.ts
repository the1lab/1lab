// Much smaller entrypoint file that only knows how to apply the users'
// settings from localStorage. This file compiles to ~1KiB of JS; it's
// totally fine to block on, unlike the ever-growing main.js.

import "./lib/settings";
