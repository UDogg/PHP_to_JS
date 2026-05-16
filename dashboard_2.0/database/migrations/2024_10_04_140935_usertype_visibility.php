<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        //
        if(!Schema::hasColumn('usertypes', 'usertype_visibility')) {
            Schema::table('usertypes', function (Blueprint $table) {
                $table->enum('is_visible', ['Y', 'N'])->after('is_active')->default('Y');
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        schema::dropColumns('usertypes', ['is_visible']);
    }
};
