class Criterion{
private:
	int targetInstruction;

}

class SlicingMethod {
public:
	SlicingMethod(string fileName);
	virtual shared_ptr<Module> getSlice(Criterion c);
private:
	shared_ptr<Module> originalProgram;
}