.PHONY: check chapter site serve
check:
	python3 tools/check.py
chapter:
	python3 tools/check.py --chapter $(CHAPTER)
site:
	python3 tools/build.py
serve: site
	python3 -m http.server 8000 --bind 127.0.0.1 --directory dist
