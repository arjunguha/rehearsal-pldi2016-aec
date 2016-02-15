TRIALS=1
.PHONY = all clean

all: idempotence.pdf determinism.pdf sizes.pdf
	@echo "Complete.\nSee idempotence.pdf, determinism.pdf, and sizes.pdf."

clean:
	rm -f sizes.csv idempotence.csv determinism.csv sizes.pdf idempotence.pdf determinism.pdf

sizes.csv:
	(cd ..; scala scripts/Benchmarks.scala sizes results/sizes.csv)

sizes.pdf: sizes.csv
	(cd ../scripts; R --file=sizes.r)

idempotence.csv:
	(cd ..; scala scripts/Benchmarks.scala idempotence $(TRIALS) results/idempotence.csv)

idempotence.pdf: idempotence.csv
	(cd ../scripts; R --file=idempotence.r)

determinism.csv:
	(cd ..; scala scripts/Benchmarks.scala determinism $(TRIALS) results/determinism.csv)

determinism.pdf: determinism.csv
	(cd ../scripts; R --file=determinism.r)
