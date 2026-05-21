(sort "term")

(sort "wff")

;; Define "term" and "wff"
(term "tze" ( ( "term")))

(term "tpl" ( ( "term") ( "term") ( "term")))

(term "weq" ( ( "term") ( "term") ( "wff")))

(term "wim" ( ( "wff") ( "wff") ( "wff")))

;; State the axioms
(axiom "a1" (!! ( ("t" ( "term")) ("r" ( "term")) ("s" ( "term")))  ("wim" ("weq" "t" "r") ("wim" ("weq" "t" "s") ("weq" "r" "s")))))

(axiom "a2" (!! ( ("t" ( "term")))  ("weq" ("tpl" "t" "tze") "t")))

(axiom "mp" (!! ( ("P" ( "wff")) ("Q" ( "wff")))  "P" ("wim" "P" "Q") "Q"))

;; Prove a theorem (Contributed by ?who?, 11-Jan-2026.)
(theorem "th1" (for ("t" ( "term"))) (for) (for) ("weq" "t" "t")
  ("mp" ("weq" ("tpl" "t" "tze") "t") ("weq" "t" "t") ("a2" "t") ("mp" ("weq" ("tpl" "t" "tze") "t") ("wim" ("weq" ("tpl" "t" "tze") "t") ("weq" "t" "t")) ("a2" "t") ("a1" ("tpl" "t" "tze") "t" "t"))))

