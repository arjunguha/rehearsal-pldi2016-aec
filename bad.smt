(declare-sort hash 0)

(declare-const hash1 hash)

(assert (distinct hash1))

(declare-datatypes () ( (stat (IsDir) (DoesNotExist) (IsFile (hash hash))) ))

(declare-const path2 stat)

(declare-const path3 stat)

(declare-const path4 stat)

(declare-const path5 stat)

(declare-const isErr6 Bool)

(assert (not (or (and (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (or (ite (is-IsFile path2) (or (or isErr6 (not (is-IsFile path2))) (not (and (= DoesNotExist DoesNotExist) (= path3 IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)) (not (and (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (= (ite (is-IsFile path2) path5 (ite (= path2 DoesNotExist) path5 path5)) IsDir)))) (ite (is-IsFile path2) (or (or isErr6 (not (is-IsFile path2))) (not (and (= DoesNotExist DoesNotExist) (= path3 IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6))) (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (or (ite (is-IsFile path2) (or (or isErr6 (not (is-IsFile path2))) (not (and (= DoesNotExist DoesNotExist) (= path3 IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)) (not (and (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (= (ite (is-IsFile path2) path5 (ite (= path2 DoesNotExist) path5 path5)) IsDir)))) (ite (is-IsFile path2) (or (or isErr6 (not (is-IsFile path2))) (not (and (= DoesNotExist DoesNotExist) (= path3 IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)))) (and (and (not (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (or (ite (is-IsFile path2) (or (or isErr6 (not (is-IsFile path2))) (not (and (= DoesNotExist DoesNotExist) (= path3 IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)) (not (and (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (= (ite (is-IsFile path2) path5 (ite (= path2 DoesNotExist) path5 path5)) IsDir)))) (ite (is-IsFile path2) (or (or isErr6 (not (is-IsFile path2))) (not (and (= DoesNotExist DoesNotExist) (= path3 IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)))) (not (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (or (ite (is-IsFile path2) (or (or isErr6 (not (is-IsFile path2))) (not (and (= DoesNotExist DoesNotExist) (= path3 IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)) (not (and (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (= (ite (is-IsFile path2) path5 (ite (= path2 DoesNotExist) path5 path5)) IsDir)))) (ite (is-IsFile path2) (or (or isErr6 (not (is-IsFile path2))) (not (and (= DoesNotExist DoesNotExist) (= path3 IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6))))) (and (and (and (= (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (ite (is-IsFile path2) (IsFile hash1) (ite (= path2 DoesNotExist) (IsFile hash1) path2)) (ite (is-IsFile path2) (IsFile hash1) (ite (= path2 DoesNotExist) (IsFile hash1) path2))) (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (ite (is-IsFile path2) (IsFile hash1) (ite (= path2 DoesNotExist) (IsFile hash1) path2)) (ite (is-IsFile path2) (IsFile hash1) (ite (= path2 DoesNotExist) (IsFile hash1) path2)))) (= (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (ite (is-IsFile path2) path3 (ite (= path2 DoesNotExist) path3 path3)) (ite (is-IsFile path2) path3 (ite (= path2 DoesNotExist) path3 path3))) (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (ite (is-IsFile path2) path3 (ite (= path2 DoesNotExist) path3 path3)) (ite (is-IsFile path2) path3 (ite (= path2 DoesNotExist) path3 path3))))) (= (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (IsFile hash1) (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4))) (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (IsFile hash1) (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4))))) (= (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (ite (is-IsFile path2) path5 (ite (= path2 DoesNotExist) path5 path5)) (ite (is-IsFile path2) path5 (ite (= path2 DoesNotExist) path5 path5))) (ite (= (ite (is-IsFile path2) path4 (ite (= path2 DoesNotExist) path4 path4)) DoesNotExist) (ite (is-IsFile path2) path5 (ite (= path2 DoesNotExist) path5 path5)) (ite (is-IsFile path2) path5 (ite (= path2 DoesNotExist) path5 path5)))))))))

(check-sat)

(declare-sort hash 0)

(declare-const hash1 hash)

(assert (distinct hash1))

(declare-datatypes () ( (stat (IsDir) (DoesNotExist) (IsFile (hash hash))) ))

(declare-const path2 stat)

(declare-const path3 stat)

(declare-const path4 stat)

(declare-const path5 stat)

(declare-const isErr6 Bool)

(assert (not (or (and (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (or (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (is-IsFile (ite (= path2 DoesNotExist) path4 path4)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (and (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (or (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (is-IsFile (ite (= path2 DoesNotExist) path4 path4)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (and (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)))) (and (and (not (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (or (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (is-IsFile (ite (= path2 DoesNotExist) path4 path4)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (and (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)))) (not (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (or (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (is-IsFile (ite (= path2 DoesNotExist) path4 path4)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (and (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6))))) (and (and (and (= (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) (IsFile hash1) path2) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) (IsFile hash1) path2) (ite (= path2 DoesNotExist) (IsFile hash1) path2))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) (IsFile hash1) path2) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) (IsFile hash1) path2) (ite (= path2 DoesNotExist) (IsFile hash1) path2)))) (= (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) path3 path3) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) path3 path3) (ite (= path2 DoesNotExist) path3 path3))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) path3 path3) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) path3 path3) (ite (= path2 DoesNotExist) path3 path3))))) (= (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (IsFile hash1) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (IsFile hash1) (ite (= path2 DoesNotExist) path4 path4))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (IsFile hash1) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (IsFile hash1) (ite (= path2 DoesNotExist) path4 path4))))) (= (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) path5 path5) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) path5 path5) (ite (= path2 DoesNotExist) path5 path5))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) path5 path5) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) path5 path5) (ite (= path2 DoesNotExist) path5 path5)))))))))

(check-sat)

(declare-sort hash 0)

(declare-const hash1 hash)

(assert (distinct hash1))

(declare-datatypes () ( (stat (IsDir) (DoesNotExist) (IsFile (hash hash))) ))

(declare-const path2 stat)

(declare-const path3 stat)

(declare-const path4 stat)

(declare-const path5 stat)

(declare-const isErr6 Bool)

(assert (not (or (and (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (or (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (is-IsFile (ite (= path2 DoesNotExist) path4 path4)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (and (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (or (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (is-IsFile (ite (= path2 DoesNotExist) path4 path4)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (and (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)))) (and (and (not (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (or (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (is-IsFile (ite (= path2 DoesNotExist) path4 path4)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (and (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6)))) (not (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (or (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (is-IsFile (ite (= path2 DoesNotExist) path4 path4)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (or (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6) (not (and (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (= (ite (= path2 DoesNotExist) path5 path5) IsDir)))) (ite (= path2 DoesNotExist) (or isErr6 (not (and (= path2 DoesNotExist) (= path3 IsDir)))) isErr6))))) (and (and (and (= (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) (IsFile hash1) path2) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) (IsFile hash1) path2) (ite (= path2 DoesNotExist) (IsFile hash1) path2))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) (IsFile hash1) path2) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) (IsFile hash1) path2) (ite (= path2 DoesNotExist) (IsFile hash1) path2)))) (= (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) path3 path3) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) path3 path3) (ite (= path2 DoesNotExist) path3 path3))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) path3 path3) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) path3 path3) (ite (= path2 DoesNotExist) path3 path3))))) (= (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (IsFile hash1) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (IsFile hash1) (ite (= path2 DoesNotExist) path4 path4))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (IsFile hash1) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (IsFile hash1) (ite (= path2 DoesNotExist) path4 path4))))) (= (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) path5 path5) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) path5 path5) (ite (= path2 DoesNotExist) path5 path5))) (ite (is-IsFile (ite (= path2 DoesNotExist) path4 path4)) (ite (= path2 DoesNotExist) path5 path5) (ite (= (ite (= path2 DoesNotExist) path4 path4) DoesNotExist) (ite (= path2 DoesNotExist) path5 path5) (ite (= path2 DoesNotExist) path5 path5)))))))))

(check-sat)

(declare-sort hash 0)

(declare-const hash1 hash)

(declare-const hash2 hash)

(assert (distinct hash1 hash2))

(declare-datatypes () ( (stat (IsDir) (DoesNotExist) (IsFile (hash hash))) ))

(declare-const path3 stat)

(declare-const path4 stat)

(declare-const path5 stat)

(declare-const path6 stat)

(declare-const isErr7 Bool)

(assert (not (or (and (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (or (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (is-IsFile (ite (= path3 DoesNotExist) path5 path5)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (and (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (or (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (is-IsFile (ite (= path3 DoesNotExist) path5 path5)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (and (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7)))) (and (and (not (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (or (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (is-IsFile (ite (= path3 DoesNotExist) path5 path5)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (and (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7)))) (not (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (or (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (is-IsFile (ite (= path3 DoesNotExist) path5 path5)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (and (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7))))) (and (and (and (= (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) (IsFile hash1) path3) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) (IsFile hash1) path3) (ite (= path3 DoesNotExist) (IsFile hash1) path3))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) (IsFile hash1) path3) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) (IsFile hash1) path3) (ite (= path3 DoesNotExist) (IsFile hash1) path3)))) (= (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) path4 path4) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) path4 path4) (ite (= path3 DoesNotExist) path4 path4))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) path4 path4) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) path4 path4) (ite (= path3 DoesNotExist) path4 path4))))) (= (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (IsFile hash2) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (IsFile hash2) (ite (= path3 DoesNotExist) path5 path5))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (IsFile hash2) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (IsFile hash2) (ite (= path3 DoesNotExist) path5 path5))))) (= (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) path6 path6) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) path6 path6) (ite (= path3 DoesNotExist) path6 path6))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) path6 path6) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) path6 path6) (ite (= path3 DoesNotExist) path6 path6)))))))))

(check-sat)

(declare-sort hash 0)

(declare-datatypes () ( (stat (IsDir) (DoesNotExist) (IsFile (hash hash))) ))

(declare-const isErr1 Bool)

(assert (not (or (and isErr1 isErr1) (and (and (not isErr1) (not isErr1)) true))))

(check-sat)

(declare-sort hash 0)

(declare-const hash1 hash)

(declare-const hash2 hash)

(assert (distinct hash1 hash2))

(declare-datatypes () ( (stat (IsDir) (DoesNotExist) (IsFile (hash hash))) ))

(declare-const path3 stat)

(declare-const path4 stat)

(declare-const path5 stat)

(declare-const path6 stat)

(declare-const isErr7 Bool)

(assert (not (or (and (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (or (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (is-IsFile (ite (= path3 DoesNotExist) path5 path5)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (and (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (or (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (is-IsFile (ite (= path3 DoesNotExist) path5 path5)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (and (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7)))) (and (and (not (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (or (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (is-IsFile (ite (= path3 DoesNotExist) path5 path5)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (and (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7)))) (not (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (or (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (is-IsFile (ite (= path3 DoesNotExist) path5 path5)))) (not (and (= DoesNotExist DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (or (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7) (not (and (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (= (ite (= path3 DoesNotExist) path6 path6) IsDir)))) (ite (= path3 DoesNotExist) (or isErr7 (not (and (= path3 DoesNotExist) (= path4 IsDir)))) isErr7))))) (and (and (and (= (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) (IsFile hash1) path3) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) (IsFile hash1) path3) (ite (= path3 DoesNotExist) (IsFile hash1) path3))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) (IsFile hash1) path3) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) (IsFile hash1) path3) (ite (= path3 DoesNotExist) (IsFile hash1) path3)))) (= (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) path4 path4) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) path4 path4) (ite (= path3 DoesNotExist) path4 path4))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) path4 path4) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) path4 path4) (ite (= path3 DoesNotExist) path4 path4))))) (= (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (IsFile hash2) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (IsFile hash2) (ite (= path3 DoesNotExist) path5 path5))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (IsFile hash2) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (IsFile hash2) (ite (= path3 DoesNotExist) path5 path5))))) (= (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) path6 path6) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) path6 path6) (ite (= path3 DoesNotExist) path6 path6))) (ite (is-IsFile (ite (= path3 DoesNotExist) path5 path5)) (ite (= path3 DoesNotExist) path6 path6) (ite (= (ite (= path3 DoesNotExist) path5 path5) DoesNotExist) (ite (= path3 DoesNotExist) path6 path6) (ite (= path3 DoesNotExist) path6 path6)))))))))

(check-sat)

(declare-sort hash 0)

(declare-const hash1 hash)

(declare-const hash2 hash)

(assert (distinct hash1 hash2))

(declare-datatypes () ( (stat (IsDir) (DoesNotExist) (IsFile (hash hash))) ))

(declare-const path3 stat)

(declare-const path4 stat)

(declare-const path5 stat)

(declare-const path6 stat)

(declare-const path7 stat)

(declare-const path8 stat)

(declare-const path9 stat)

(declare-const path10 stat)

(declare-const path11 stat)

(declare-const path12 stat)

(declare-const path13 stat)

(declare-const path14 stat)

(declare-const path15 stat)

(declare-const path16 stat)

(declare-const path17 stat)

(declare-const path18 stat)

(declare-const path19 stat)

(declare-const path20 stat)

(declare-const path21 stat)

(declare-const path22 stat)

(declare-const path23 stat)

(declare-const path24 stat)

(declare-const path25 stat)

(declare-const path26 stat)

(declare-const path27 stat)

(declare-const path28 stat)

(declare-const path29 stat)

(declare-const path30 stat)

(declare-const path31 stat)

(declare-const path32 stat)

(declare-const path33 stat)

(declare-const path34 stat)

(declare-const path35 stat)

(declare-const path36 stat)

(declare-const path37 stat)

(declare-const path38 stat)

(declare-const path39 stat)

(declare-const path40 stat)

(declare-const path41 stat)

(declare-const path42 stat)

(declare-const path43 stat)

(declare-const path44 stat)

(declare-const isErr45 Bool)

(declare-const choice46 Bool)

(declare-const choice47 Bool)

(declare-sort hash 0)

(declare-const hash1 hash)

(declare-const hash2 hash)

(assert (distinct hash1 hash2))

(declare-datatypes () ( (stat (IsDir) (DoesNotExist) (IsFile (hash hash))) ))

(declare-const path3 stat)

(declare-const path4 stat)

(declare-const path5 stat)

(declare-const path6 stat)

(declare-const path7 stat)

(declare-const path8 stat)

(declare-const path9 stat)

(declare-const path10 stat)

(declare-const path11 stat)

(declare-const path12 stat)

(declare-const path13 stat)

(declare-const path14 stat)

(declare-const path15 stat)

(declare-const path16 stat)

(declare-const path17 stat)

(declare-const path18 stat)

(declare-const path19 stat)

(declare-const path20 stat)

(declare-const path21 stat)

(declare-const path22 stat)

(declare-const path23 stat)

(declare-const path24 stat)

(declare-const path25 stat)

(declare-const path26 stat)

(declare-const path27 stat)

(declare-const path28 stat)

(declare-const path29 stat)

(declare-const path30 stat)

(declare-const path31 stat)

(declare-const path32 stat)

(declare-const path33 stat)

(declare-const path34 stat)

(declare-const path35 stat)

(declare-const path36 stat)

(declare-const path37 stat)

(declare-const path38 stat)

(declare-const path39 stat)

(declare-const path40 stat)

(declare-const path41 stat)

(declare-const path42 stat)

(declare-const path43 stat)

(declare-const path44 stat)

(declare-const isErr45 Bool)

(declare-const choice46 Bool)

(declare-const choice47 Bool)

