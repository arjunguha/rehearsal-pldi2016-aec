@model $rootnamespace$.Models.ChangePasswordModel
@{
    ViewBag.Title = "Settings";
    Layout = "~/Views/Shared/_Folder.cshtml";
    ViewBag.SitemapProvider = "Account";
}

<div class="page-header">
    <h1>Change Password</h1>
</div>
<div class="alert alert-block alert-info">
    <p>
        Use the form below to change your password.
    </p>
    <p>
        New passwords are required to be a minimum of 6
        characters in length.
    </p>
</div>
<div class="row-fluid">
    @using (Html.BeginForm("Settings", "Account", FormMethod.Post, new { @class = "form-horizontal" }))
    {
        @Html.ValidationSummary(true, "Password change was unsuccessful. Please correct the errors and try again.", new { @class = "alert alert-block alert-error" })
            
        @Html.EditorForModel("Bootstrap/Bootstrap.Form")
        
        <div class="form-actions">
            <input type="submit" value="Change Password" class="btn btn-primary" />
        </div>                    
    }
</div>
