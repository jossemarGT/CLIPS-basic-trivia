;;; Este objetivo será satisfecho si se determinó el personaje
(goal is el.personaje.es)

;;; Respuestas permitidas
(legalanswer (answers "si" "no" "probablemente si" "posiblemente si" "posiblemente no" "probablemente no" "no se") )
(solidanswer si no)
(partialanswer are posiblemente.si posiblemente.no probablemente.si probablemente.no no.se)
(nullanswer is no.se)
(partialyes are posiblemente.si probablemente.si)
(partialno  are posiblemente.no probablemente.no)

;;; Respuesta final
(answer is "Yo creo que tu personaje es" custom.character)
