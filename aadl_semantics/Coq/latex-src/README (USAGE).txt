How to compile...
-----------------
Open the desired identity report (tr, tr draft, or tn) in a LaTeX editor.

After making necessary changes to the document...
	1. Compile the document initially using PDFLaTeX to build the framework.
	2. Run BibTeX to create the bibliography files (If you have references).
	3. Run MakeIndex using the parameters outlined in the end of
	   the Introduction chapter to build the report index (If using one).
	4. Run PDFLaTeX again to recompile with the bibliography and index.
	5. Run PDFLaTeX one last time to update all of the labels and links. 

--------------------------------------------------------------------------------------------

Description of files:
---------------------
README (USAGE).txt	This file.



Depending on the document format needed, one of the following files
needs to be modified and compiled to produce the desired PDF output formatting.

	techreport.tex		The main TR/TR Draft/TN document file.

		"Use the commented out code at the top of this file to choode between
		TR, TR Draft, SR, and TN document syles and whether or not to display
		the header Draft Pending RRO Approval message." Be sure to format the
		document number properly in here too.



Other Files:

	identity-report.ist		Index style file for the TR/TR Draft/TN/SR document index

	SEIreport.sty			This is the master style file that sefines the
					styling rules for the master document tex files.

	techreport.pdf		Output PDF for the TR/TR Draft/TN/SR document.



Description of Folders
	assets		This folder contains any document images.
	assets/bib	This folder contains any reference / bibliography files.
	content		This folder contains all of the pages containing the report contents;
			Includes front matter, report body, and end matter.