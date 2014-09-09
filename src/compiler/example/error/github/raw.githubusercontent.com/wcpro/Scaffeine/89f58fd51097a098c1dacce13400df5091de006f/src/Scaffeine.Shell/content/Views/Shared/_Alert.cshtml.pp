@if (TempData["Success"] != null)
{                
    <div class="alert alert-success">
        @TempData["Success"]
    </div>
}
@if (TempData["Error"] != null)
{                
    <div class="alert alert-danger">
        @TempData["Error"]
    </div>
}
@if (TempData["Information"] != null)
{                
    <div class="alert alert-info">
        @TempData["Information"]
    </div>
}