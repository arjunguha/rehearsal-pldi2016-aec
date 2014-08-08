@model $rootnamespace$.Models.LogOnModel
@{
    ViewBag.Title = "Log On";
}
@section container{
    <div class="page-header">
        <h1>Already Have An Account? <small class="pull-right">
            @Html.ActionLink("Register", "Register")
            if you don't have an account. </small>
        </h1>
    </div>
    <div class="row">
        @using (Html.BeginForm("Logon", "Account", FormMethod.Post, new { @class = "form-horizontal" }))
        {
            @Html.ValidationSummary(true, "Log on was unsuccessful. Please correct the errors and try again.", new { @class = "alert alert-block alert-error" })
           
                @Html.EditorForModel("Bootstrap/Bootstrap.Form")           
                                             
            <div class="form-actions">
                <input type="submit" value="Log On" class="btn btn-primary" />
                <a href="@Url.Action("ForgotPassword", "Account")">I forgot my password</a>
            </div>
            
        }
    </div>
}
