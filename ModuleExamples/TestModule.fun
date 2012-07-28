module TestModule

-- Si descomentamos alguno de los dos, producimos imports ciclicos.
--import TestModule1
--import TestModule2


-- Esta es la función que de momento chequea bien como derivación.
let fun hola : Int :-> Int
hola x = 0
deriving from otroteorema

-- Acá esta la especificación de la función de arriba.
let spec hola x = 0

-- Este esta es la prueba de la derivación.
begin proof otroteorema [~ hh:hola%(x)=0 ~]
hola%(x)
= { hh }
0
end proof

