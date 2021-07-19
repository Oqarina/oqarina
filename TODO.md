# List of pending items

## AADL Instance Textual Notation

- [ ] the original Xtext files reuses elements of the AADLv2 declarative xtext grammar. This is a pain especially for PropertyExpression, we should provide a simpler grammar for this part
- [ ] modes and flows are not supported. it is unclear this is desirable at this stage
- [ ] connections requires some thoughts
- [ ] the lexer is manually written, lexing elements with a space like "virtual bus" could be changed for clarity. E.g. we have "virtual group" but "eventPort"
- [ ] some elements are optional in the gramamr, for instance {}. We could have them in all cases. Compare p_SystemInstance and p_ComponentInstance. p_SystemInstance forces {}, p_ComponentInstance has them optional.
- [ ] the instance notation loses the information on the types in case of extensions, see test02 for an illustration

## Properties

- [x] wellformedness of a property set, of a property type
- [ ] property value correctly applies to a component
- [ ] add units to range constraints
- [ ] inherit?
- [ ] reference to property constant in proprety type? see aadl_thread_properties

## Property Sets

- [ ] investigate type checking of Communication_Properties_PS

