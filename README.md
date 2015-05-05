rehearsal
=========

## License

You do not have a license to use this software.

## Installing Z3 (for z3analysis)

- Checkout Z3 from [https://github.com/Z3Prover/z3]
- Build as follows:

       python scripts/mk_make.py --java
       cd build
       make
       sudo make install
- On MacOS X
  + Move `/Library/lib/com.microsoft.z3.jar` to `z3analysis/lib`
  + Move `/Library/lib/libz3java.dylib` to `/usr/lib/java`
  + Move `/Library/lib/libz3.dylib` to `/usr/lib`


