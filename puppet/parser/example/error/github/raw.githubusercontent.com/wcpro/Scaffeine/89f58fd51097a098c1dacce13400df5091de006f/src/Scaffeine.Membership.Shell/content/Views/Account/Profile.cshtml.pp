@model $rootnamespace$.Models.ProfileModel
@{
    ViewBag.Title = "Profile";
    Layout = "~/Views/Shared/_Folder.cshtml";
    ViewBag.SitemapProvider = "Account";

    Bundles.Reference("content/custom/hide-breadcrumb.less", "custom");
}

<div class="page-header">
    <h1>
        Your Profile</h1>
</div>
<div class="row-fluid">

    @using (Html.BeginForm("Profile", "Account", FormMethod.Post, new { @class = "form-horizontal" }))
    {
        @Html.ValidationSummary(true, "Unable to update profile. Please correct the errors and try again.", new { @class = "alert alert-block alert-error" })
        
        @Html.EditorForModel("Bootstrap/Bootstrap.Form")
        
        <div class="form-actions">
            <input type="submit" value="Update" class="btn btn-primary" />
        </div>        
    }
</div>