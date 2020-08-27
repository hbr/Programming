redblack.html: red_black_tree.md style.css
	pandoc -o redblack.html \
	    --toc --standalone --toc-depth=2  \
	    style.css           \
	    red_black_tree.md   \
	    --metadata-file meta.yaml



redblack.pdf: red_black_tree.md
	pandoc -o redblack.pdf \
	    red_black_tree.md   \
	    --metadata-file meta.yaml
