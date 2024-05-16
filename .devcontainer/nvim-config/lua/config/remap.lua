vim.g.mapleader = " "
vim.keymap.set("n", "<leader>pv", vim.cmd.Ex)
vim.keymap.set("n", "<leader>w", "<Cmd>w<CR>")

vim.keymap.set("n", "K", "<Cmd>lua vim.lsp.buf.hover()<CR>")

local idr = require('idris2.code_action')
vim.keymap.set("n", "<leader>pc", idr.case_split)
vim.keymap.set("n", "<leader>pe", idr.expr_search)
vim.keymap.set("n", "<leader>phe", idr.expr_search_hints)
vim.keymap.set("n", "<leader>pa", idr.add_clause)
vim.keymap.set("n", "<leader>pl", idr.make_lemma)
vim.keymap.set("n", "gl", vim.diagnostic.open_float)

