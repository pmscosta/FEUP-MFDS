datatype Sex = Masculine | Feminine
datatype CivilState = Single | Married | Divorced | Widow | Dead
 
class Person
{
    const name: string; // ‘const’ for immutable fields
    const sex: Sex;
    const mother: Person?; // ‘?’ to allow null
    const father: Person?;
    var spouse: Person?;
    var civilState: CivilState;
 
    constructor (name: string, sex: Sex, mother: Person?, father: Person?)
    {
        this.name := name;
        this.sex := sex;
        this.mother := mother;
        this.father := father;
        this.spouse := null;
        this.civilState := Single;
    }

    predicate Valid()
        reads this
        reads this.spouse
    {
        (this.civilState == Married <==> this.spouse != null )
        && 
        (this.mother != null ==> this.mother.sex == Feminine)
        &&
        (this.father != null ==> this.father.sex == Masculine)
        &&
        (this.civilState == Married ==> this.spouse.sex != this.sex && this.spouse.civilState == Married)
        &&
        (this.spouse != null ==> this == this.spouse.spouse)
        &&
        (this.spouse != this)

    }
 
    method marry(spouse: Person)
       modifies this
       modifies spouse
       requires this.spouse == null
       requires spouse.spouse == null
       requires spouse.sex != this.sex
       requires Valid()
       ensures Valid()
    {
        spouse.spouse := this;
        spouse.civilState := Married;
        this.spouse := spouse;
        this.civilState := Married;
    }
 
    method divorce()
        modifies this
        modifies this.spouse
        requires this.spouse != null
        requires Valid()
        ensures Valid()
    {
        spouse.spouse := null;
        spouse.civilState := Divorced;
        this.spouse := null;
        this.civilState := Divorced;
    }
 
    method die()
    {
        if spouse != null
        {
            spouse.spouse := null;
            spouse.civilState := Widow;
        }
        this.spouse := null;
        this.civilState := Dead;
    }
}
