How I obtained this code:
-------------------------
Deleted "Polymorphic" in general. (Needed to update a hypothesis name to compile everything, though very straightforward.)
Extracted Cut.
Copied .hs files here.
Added Main file with pretty printing and examples.
Load Main, call cut_examples in Main.

How I obtained the examples that I copied and pasted into Main.hs:
------------------------------------------------------------------
Called "Recursive Extraction" or "Extraction" on the examples found in cut_extraction_example.v.
Copied and pasted output into Main.hs.
Then needed to update the names manually e.g. from "List" to "Datatypes.Coq_list". This is a pain and need to think of better way.

Moving forward:
---------------
Figure out a way of pretty printing. E.g. tree structure?
Figure out a way to get examples as well as extracted cut theorem directly.
