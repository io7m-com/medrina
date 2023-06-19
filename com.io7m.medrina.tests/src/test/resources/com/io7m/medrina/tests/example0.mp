(Medrina 1 0)

(Rule
  (Name "rule0")
  (Description "Rule 0")
  (Conclusion Deny)
  (MatchSubject
    [And (Or [WithAnyRolesFrom x y z]
             [WithAllRolesFrom a b])
         (Or True False)])
  (MatchObject
    [And (Or [WithType a] [WithType b])
         (Or True False)
         (Or [WithAnyAttributesFrom [Attribute "x" "y"] [Attribute "a" "b"]]
             [WithAllAttributesFrom [Attribute "m" "n"] [Attribute "o" "p"]])])
  (MatchAction
    [And (Or [WithName a] [WithName b])
         (Or True False)]))


(Rule
  (Name "rule1")
  (Description "Rule 1")
  (Conclusion Allow)
  (MatchSubject False)
  (MatchObject False)
  (MatchAction False))
