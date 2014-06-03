@model $rootnamespace$.Models.RegisterModel
@{
    ViewBag.Title = "Register";
}
@section container{
    <div class="page-header">
        <h1>Create A New Account
        </h1>
    </div>
    <div class="row">
        @using (Html.BeginForm("Register", "Account", FormMethod.Post, new { @class = "form-horizontal" }))
        {                                 
            @Html.ValidationSummary(true, "Account creation was unsuccessful. Please correct the errors and try again.", new { @class = "alert alert-block alert-error" })
                                   
            @Html.EditorForModel("Bootstrap/Bootstrap.Form")         
            
            <div class="form-actions">
                <input type="submit" value="Create Account" class="btn btn-primary" />
                <input type="reset" value="Clear Form" class="btn" title="Remove all the data from the form." />
            </div>                          
        }
    </div>
}