(medrina 1 0)

(deny
  (subject
    [and (or [with-any-roles x y z]
             [with-all-roles a b])
         (or true false)])
  (object
    [and (or [with-type a] [with-type b])
         (or true false)])
  (action
    [and (or [with-name a] [with-name b])
         (or true false)]))

(allow
  (subject false)
  (object false)
  (action false))
