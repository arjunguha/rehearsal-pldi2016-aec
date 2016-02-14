sizes.csv:
	(cd ..; scala scripts/Benchmarks.scala sizes results/sizes.csv)

sizes.pdf: sizes.csv
	(cd ../scripts; R --file=sizes.r)

idempotence.csv:
	(cd ..; scala scripts/Benchmarks.scala idempotence 1 results/idempotence.csv)

idempotence.pdf: idempotence.csv
	(cd ../scripts; R --file=idempotence.r)

determinism.csv:
	(cd ..; scala scripts/Benchmarks.scala determinism 1 results/determinism.csv)

determinism.pdf: determinism.csv
	(cd ../scripts; R --file=determinism.r)
