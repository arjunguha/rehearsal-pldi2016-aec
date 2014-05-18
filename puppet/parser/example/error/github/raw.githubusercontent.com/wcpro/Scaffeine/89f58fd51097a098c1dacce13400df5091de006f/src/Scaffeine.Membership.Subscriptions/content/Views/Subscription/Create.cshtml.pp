@model $rootnamespace$.Models.CreditCardModel

@{
    ViewBag.Title = "Create Subscription";
}
@section container{
    <div class="page-header">
        <h1>Create A Subscription</h1>
    </div>
    <div class="row">
        @using (Html.BeginForm("Create", "Subscription", FormMethod.Post, new { @class = "form-horizontal" }))
        {                                                        
            @Html.EditorForModel("Bootstrap/Bootstrap.Form")         
            
            <div class="form-actions">
                <input type="submit" value="Update Credit Card Information" class="btn btn-primary" />
                <input type="reset" value="Clear Form" class="btn" title="Remove all the data from the form." />
            </div>
        }
    </div>
}