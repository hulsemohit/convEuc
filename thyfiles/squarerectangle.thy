theory squarerectangle
	imports Axioms Definitions Theorems
begin

theorem squarerectangle:
	assumes: `axioms`
		"square A B C D"
	shows: "rectangle A B C D"
proof -
	have "parallelogram A B C D" using squareparallelogram[OF `axioms` `square A B C D`] .
	have "ang_right D A B" using square_f[OF `axioms` `square A B C D`] by blast
	have "rectangle A B C D" using PGrectangle[OF `axioms` `parallelogram A B C D` `ang_right D A B`] .
	thus ?thesis by blast
qed

end