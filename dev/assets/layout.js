(function () {
    "use strict";

    const storageKey = "verified-samplers-doc-width";

    function apply(mode, button) {
        const full = mode === "full";
        document.documentElement.classList.toggle(
            "verified-samplers-full-width", full);
        button.setAttribute("aria-pressed", String(full));
        button.title = full ? "Use normal-width documentation" :
            "Use full-width documentation";
        const label = button.querySelector(".docs-label");
        if (label) label.textContent = full ? "Normal width" : "Full width";
    }

    function initialize() {
        const controls = document.querySelector("#documenter .docs-navbar .docs-right");
        if (!controls || document.getElementById("verified-samplers-width-toggle")) return;

        const button = document.createElement("button");
        button.id = "verified-samplers-width-toggle";
        button.className = "docs-navbar-link";
        button.type = "button";
        button.innerHTML = '<span class="fa-solid fa-arrows-left-right"></span>' +
            '<span class="docs-label is-hidden-touch">Full width</span>';
        controls.insertBefore(button, controls.firstChild);

        let mode = "normal";
        try {
            mode = window.localStorage.getItem(storageKey) || mode;
        } catch (_) {
            // Storage can be unavailable in privacy-restricted contexts.
        }
        apply(mode, button);
        button.addEventListener("click", function () {
            mode = document.documentElement.classList.contains(
                "verified-samplers-full-width") ? "normal" : "full";
            try {
                window.localStorage.setItem(storageKey, mode);
            } catch (_) {
                // The toggle still works for the current page without storage.
            }
            apply(mode, button);
        });
    }

    if (document.readyState === "loading") {
        document.addEventListener("DOMContentLoaded", initialize);
    } else {
        initialize();
    }
})();
