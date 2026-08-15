document.addEventListener("DOMContentLoaded", async () => {
  const blocks = document.querySelectorAll("pre > code.language-mermaid");
  if (blocks.length === 0) return;

  for (const block of blocks) {
    const diagram = document.createElement("div");
    diagram.className = "mermaid";
    diagram.textContent = block.textContent;
    block.parentElement.replaceWith(diagram);
  }

  const mermaid = (await import(
    "https://cdn.jsdelivr.net/npm/mermaid@11/dist/mermaid.esm.min.mjs"
  )).default;
  mermaid.initialize({ startOnLoad: false, securityLevel: "strict" });
  await mermaid.run({ querySelector: ".mermaid" });
});
