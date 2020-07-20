.PHONY: redblack


redblack:
	make -C redblack/doc redblack.html; \
	make -C redblack/doc redblack.pdf;  \


gh-pages: redblack
	cp redblack/doc/redblack.html gh-pages/redblack/doc; \
	cp redblack/doc/redblack.pdf gh-pages/redblack/doc;  \
	cp *.html gh-pages/;  \
	cp *.css  gh-pages/
